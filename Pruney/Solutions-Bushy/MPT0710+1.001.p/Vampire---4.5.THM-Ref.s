%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0710+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:31 EST 2020

% Result     : Theorem 2.18s
% Output     : Refutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 756 expanded)
%              Number of leaves         :   19 ( 256 expanded)
%              Depth                    :   35
%              Number of atoms          :  564 (6649 expanded)
%              Number of equality atoms :  150 (2168 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f526,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f59,f63,f121,f125,f180,f366,f525])).

fof(f525,plain,
    ( ~ spl5_1
    | spl5_2
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f524])).

fof(f524,plain,
    ( $false
    | ~ spl5_1
    | spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f523,f53])).

fof(f53,plain,
    ( k1_funct_1(sK0,sK3) != k1_funct_1(sK1,sK3)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl5_2
  <=> k1_funct_1(sK0,sK3) = k1_funct_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f523,plain,
    ( k1_funct_1(sK0,sK3) = k1_funct_1(sK1,sK3)
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f522,f519])).

fof(f519,plain,
    ( k1_funct_1(sK0,sK3) = k1_funct_1(k7_relat_1(sK0,sK2),sK3)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f515,f29])).

fof(f29,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( ( k1_funct_1(sK0,sK3) != k1_funct_1(sK1,sK3)
        & r2_hidden(sK3,sK2) )
      | k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) )
    & ( ! [X4] :
          ( k1_funct_1(sK0,X4) = k1_funct_1(sK1,X4)
          | ~ r2_hidden(X4,sK2) )
      | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) )
    & r1_tarski(sK2,k1_relat_1(sK1))
    & r1_tarski(sK2,k1_relat_1(sK0))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f25,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
                      & r2_hidden(X3,X2) )
                  | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) )
                & ( ! [X4] :
                      ( k1_funct_1(X0,X4) = k1_funct_1(X1,X4)
                      | ~ r2_hidden(X4,X2) )
                  | k7_relat_1(X0,X2) = k7_relat_1(X1,X2) )
                & r1_tarski(X2,k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) )
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( k1_funct_1(X1,X3) != k1_funct_1(sK0,X3)
                    & r2_hidden(X3,X2) )
                | k7_relat_1(X1,X2) != k7_relat_1(sK0,X2) )
              & ( ! [X4] :
                    ( k1_funct_1(X1,X4) = k1_funct_1(sK0,X4)
                    | ~ r2_hidden(X4,X2) )
                | k7_relat_1(X1,X2) = k7_relat_1(sK0,X2) )
              & r1_tarski(X2,k1_relat_1(X1))
              & r1_tarski(X2,k1_relat_1(sK0)) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ? [X3] :
                  ( k1_funct_1(X1,X3) != k1_funct_1(sK0,X3)
                  & r2_hidden(X3,X2) )
              | k7_relat_1(X1,X2) != k7_relat_1(sK0,X2) )
            & ( ! [X4] :
                  ( k1_funct_1(X1,X4) = k1_funct_1(sK0,X4)
                  | ~ r2_hidden(X4,X2) )
              | k7_relat_1(X1,X2) = k7_relat_1(sK0,X2) )
            & r1_tarski(X2,k1_relat_1(X1))
            & r1_tarski(X2,k1_relat_1(sK0)) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ( ? [X3] :
                ( k1_funct_1(sK0,X3) != k1_funct_1(sK1,X3)
                & r2_hidden(X3,X2) )
            | k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2) )
          & ( ! [X4] :
                ( k1_funct_1(sK0,X4) = k1_funct_1(sK1,X4)
                | ~ r2_hidden(X4,X2) )
            | k7_relat_1(sK0,X2) = k7_relat_1(sK1,X2) )
          & r1_tarski(X2,k1_relat_1(sK1))
          & r1_tarski(X2,k1_relat_1(sK0)) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ( ? [X3] :
              ( k1_funct_1(sK0,X3) != k1_funct_1(sK1,X3)
              & r2_hidden(X3,X2) )
          | k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2) )
        & ( ! [X4] :
              ( k1_funct_1(sK0,X4) = k1_funct_1(sK1,X4)
              | ~ r2_hidden(X4,X2) )
          | k7_relat_1(sK0,X2) = k7_relat_1(sK1,X2) )
        & r1_tarski(X2,k1_relat_1(sK1))
        & r1_tarski(X2,k1_relat_1(sK0)) )
   => ( ( ? [X3] :
            ( k1_funct_1(sK0,X3) != k1_funct_1(sK1,X3)
            & r2_hidden(X3,sK2) )
        | k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) )
      & ( ! [X4] :
            ( k1_funct_1(sK0,X4) = k1_funct_1(sK1,X4)
            | ~ r2_hidden(X4,sK2) )
        | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) )
      & r1_tarski(sK2,k1_relat_1(sK1))
      & r1_tarski(sK2,k1_relat_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X3] :
        ( k1_funct_1(sK0,X3) != k1_funct_1(sK1,X3)
        & r2_hidden(X3,sK2) )
   => ( k1_funct_1(sK0,sK3) != k1_funct_1(sK1,sK3)
      & r2_hidden(sK3,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
                    & r2_hidden(X3,X2) )
                | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) )
              & ( ! [X4] :
                    ( k1_funct_1(X0,X4) = k1_funct_1(X1,X4)
                    | ~ r2_hidden(X4,X2) )
                | k7_relat_1(X0,X2) = k7_relat_1(X1,X2) )
              & r1_tarski(X2,k1_relat_1(X1))
              & r1_tarski(X2,k1_relat_1(X0)) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
                    & r2_hidden(X3,X2) )
                | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) )
              & ( ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,X2) )
                | k7_relat_1(X0,X2) = k7_relat_1(X1,X2) )
              & r1_tarski(X2,k1_relat_1(X1))
              & r1_tarski(X2,k1_relat_1(X0)) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
                    & r2_hidden(X3,X2) )
                | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) )
              & ( ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,X2) )
                | k7_relat_1(X0,X2) = k7_relat_1(X1,X2) )
              & r1_tarski(X2,k1_relat_1(X1))
              & r1_tarski(X2,k1_relat_1(X0)) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              <~> ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,X2) ) )
              & r1_tarski(X2,k1_relat_1(X1))
              & r1_tarski(X2,k1_relat_1(X0)) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              <~> ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,X2) ) )
              & r1_tarski(X2,k1_relat_1(X1))
              & r1_tarski(X2,k1_relat_1(X0)) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( r1_tarski(X2,k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) )
               => ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
                <=> ! [X3] :
                      ( r2_hidden(X3,X2)
                     => k1_funct_1(X0,X3) = k1_funct_1(X1,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( r1_tarski(X2,k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) )
             => ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              <=> ! [X3] :
                    ( r2_hidden(X3,X2)
                   => k1_funct_1(X0,X3) = k1_funct_1(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t165_funct_1)).

fof(f515,plain,
    ( k1_funct_1(sK0,sK3) = k1_funct_1(k7_relat_1(sK0,sK2),sK3)
    | ~ v1_relat_1(sK0)
    | ~ spl5_3 ),
    inference(resolution,[],[f481,f30])).

fof(f30,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f481,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | k1_funct_1(k7_relat_1(X0,sK2),sK3) = k1_funct_1(X0,sK3)
        | ~ v1_relat_1(X0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f58,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,X1)
       => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_funct_1)).

fof(f58,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl5_3
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f522,plain,
    ( k1_funct_1(sK1,sK3) = k1_funct_1(k7_relat_1(sK0,sK2),sK3)
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f521,f48])).

fof(f48,plain,
    ( k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl5_1
  <=> k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f521,plain,
    ( k1_funct_1(sK1,sK3) = k1_funct_1(k7_relat_1(sK1,sK2),sK3)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f516,f31])).

fof(f31,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f516,plain,
    ( k1_funct_1(sK1,sK3) = k1_funct_1(k7_relat_1(sK1,sK2),sK3)
    | ~ v1_relat_1(sK1)
    | ~ spl5_3 ),
    inference(resolution,[],[f481,f32])).

fof(f32,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f366,plain,
    ( spl5_1
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f365])).

fof(f365,plain,
    ( $false
    | spl5_1
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f362,f70])).

fof(f70,plain,(
    sK2 = k3_xboole_0(sK2,k1_relat_1(sK0)) ),
    inference(resolution,[],[f33,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f33,plain,(
    r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f362,plain,
    ( sK2 != k3_xboole_0(sK2,k1_relat_1(sK0))
    | spl5_1
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(superposition,[],[f354,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f354,plain,
    ( sK2 != k3_xboole_0(k1_relat_1(sK0),sK2)
    | spl5_1
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f353,f71])).

fof(f71,plain,(
    sK2 = k3_xboole_0(sK2,k1_relat_1(sK1)) ),
    inference(resolution,[],[f34,f42])).

fof(f34,plain,(
    r1_tarski(sK2,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f353,plain,
    ( k3_xboole_0(k1_relat_1(sK0),sK2) != k3_xboole_0(sK2,k1_relat_1(sK1))
    | spl5_1
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f352,f40])).

fof(f352,plain,
    ( k3_xboole_0(k1_relat_1(sK0),sK2) != k3_xboole_0(k1_relat_1(sK1),sK2)
    | spl5_1
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f351,f64])).

fof(f64,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK0,X0)) = k3_xboole_0(k1_relat_1(sK0),X0) ),
    inference(resolution,[],[f29,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f351,plain,
    ( k3_xboole_0(k1_relat_1(sK1),sK2) != k1_relat_1(k7_relat_1(sK0,sK2))
    | spl5_1
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f350,f67])).

fof(f67,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0) ),
    inference(resolution,[],[f31,f41])).

fof(f350,plain,
    ( k1_relat_1(k7_relat_1(sK0,sK2)) != k1_relat_1(k7_relat_1(sK1,sK2))
    | spl5_1
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f349,f69])).

fof(f69,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(subsumption_resolution,[],[f68,f31])).

fof(f68,plain,(
    ! [X0] :
      ( v1_relat_1(k7_relat_1(sK1,X0))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f32,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f349,plain,
    ( k1_relat_1(k7_relat_1(sK0,sK2)) != k1_relat_1(k7_relat_1(sK1,sK2))
    | ~ v1_relat_1(k7_relat_1(sK1,sK2))
    | spl5_1
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f348,f171])).

fof(f171,plain,
    ( v1_funct_1(k7_relat_1(sK1,sK2))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl5_7
  <=> v1_funct_1(k7_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f348,plain,
    ( k1_relat_1(k7_relat_1(sK0,sK2)) != k1_relat_1(k7_relat_1(sK1,sK2))
    | ~ v1_funct_1(k7_relat_1(sK1,sK2))
    | ~ v1_relat_1(k7_relat_1(sK1,sK2))
    | spl5_1
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f347,f66])).

fof(f66,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK0,X0)) ),
    inference(subsumption_resolution,[],[f65,f29])).

fof(f65,plain,(
    ! [X0] :
      ( v1_relat_1(k7_relat_1(sK0,X0))
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f30,f43])).

fof(f347,plain,
    ( k1_relat_1(k7_relat_1(sK0,sK2)) != k1_relat_1(k7_relat_1(sK1,sK2))
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_funct_1(k7_relat_1(sK1,sK2))
    | ~ v1_relat_1(k7_relat_1(sK1,sK2))
    | spl5_1
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f346,f116])).

fof(f116,plain,
    ( v1_funct_1(k7_relat_1(sK0,sK2))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl5_5
  <=> v1_funct_1(k7_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f346,plain,
    ( k1_relat_1(k7_relat_1(sK0,sK2)) != k1_relat_1(k7_relat_1(sK1,sK2))
    | ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_funct_1(k7_relat_1(sK1,sK2))
    | ~ v1_relat_1(k7_relat_1(sK1,sK2))
    | spl5_1
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f345,f49])).

fof(f49,plain,
    ( k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f345,plain,
    ( k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | k1_relat_1(k7_relat_1(sK0,sK2)) != k1_relat_1(k7_relat_1(sK1,sK2))
    | ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_funct_1(k7_relat_1(sK1,sK2))
    | ~ v1_relat_1(k7_relat_1(sK1,sK2))
    | spl5_1
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f344,f329])).

fof(f329,plain,
    ( k1_funct_1(sK0,sK4(k7_relat_1(sK1,sK2),k7_relat_1(sK0,sK2))) = k1_funct_1(k7_relat_1(sK0,sK2),sK4(k7_relat_1(sK1,sK2),k7_relat_1(sK0,sK2)))
    | spl5_1
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f324,f29])).

fof(f324,plain,
    ( k1_funct_1(sK0,sK4(k7_relat_1(sK1,sK2),k7_relat_1(sK0,sK2))) = k1_funct_1(k7_relat_1(sK0,sK2),sK4(k7_relat_1(sK1,sK2),k7_relat_1(sK0,sK2)))
    | ~ v1_relat_1(sK0)
    | spl5_1
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(resolution,[],[f310,f30])).

fof(f310,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | k1_funct_1(k7_relat_1(X0,sK2),sK4(k7_relat_1(sK1,sK2),k7_relat_1(sK0,sK2))) = k1_funct_1(X0,sK4(k7_relat_1(sK1,sK2),k7_relat_1(sK0,sK2)))
        | ~ v1_relat_1(X0) )
    | spl5_1
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(resolution,[],[f308,f45])).

fof(f308,plain,
    ( r2_hidden(sK4(k7_relat_1(sK1,sK2),k7_relat_1(sK0,sK2)),sK2)
    | spl5_1
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f307,f49])).

fof(f307,plain,
    ( k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | r2_hidden(sK4(k7_relat_1(sK1,sK2),k7_relat_1(sK0,sK2)),sK2)
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f306,f171])).

fof(f306,plain,
    ( ~ v1_funct_1(k7_relat_1(sK1,sK2))
    | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | r2_hidden(sK4(k7_relat_1(sK1,sK2),k7_relat_1(sK0,sK2)),sK2)
    | ~ spl5_6 ),
    inference(trivial_inequality_removal,[],[f305])).

fof(f305,plain,
    ( sK2 != sK2
    | ~ v1_funct_1(k7_relat_1(sK1,sK2))
    | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | r2_hidden(sK4(k7_relat_1(sK1,sK2),k7_relat_1(sK0,sK2)),sK2)
    | ~ spl5_6 ),
    inference(superposition,[],[f256,f71])).

fof(f256,plain,
    ( ! [X0] :
        ( sK2 != k3_xboole_0(X0,k1_relat_1(sK1))
        | ~ v1_funct_1(k7_relat_1(sK1,X0))
        | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,X0)
        | r2_hidden(sK4(k7_relat_1(sK1,X0),k7_relat_1(sK0,sK2)),sK2) )
    | ~ spl5_6 ),
    inference(superposition,[],[f157,f40])).

fof(f157,plain,
    ( ! [X1] :
        ( sK2 != k3_xboole_0(k1_relat_1(sK1),X1)
        | ~ v1_funct_1(k7_relat_1(sK1,X1))
        | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,X1)
        | r2_hidden(sK4(k7_relat_1(sK1,X1),k7_relat_1(sK0,sK2)),sK2) )
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f152,f69])).

fof(f152,plain,
    ( ! [X1] :
        ( sK2 != k3_xboole_0(k1_relat_1(sK1),X1)
        | ~ v1_relat_1(k7_relat_1(sK1,X1))
        | ~ v1_funct_1(k7_relat_1(sK1,X1))
        | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,X1)
        | r2_hidden(sK4(k7_relat_1(sK1,X1),k7_relat_1(sK0,sK2)),sK2) )
    | ~ spl5_6 ),
    inference(superposition,[],[f120,f67])).

fof(f120,plain,
    ( ! [X4] :
        ( sK2 != k1_relat_1(X4)
        | ~ v1_relat_1(X4)
        | ~ v1_funct_1(X4)
        | k7_relat_1(sK0,sK2) = X4
        | r2_hidden(sK4(X4,k7_relat_1(sK0,sK2)),sK2) )
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl5_6
  <=> ! [X4] :
        ( sK2 != k1_relat_1(X4)
        | ~ v1_relat_1(X4)
        | ~ v1_funct_1(X4)
        | k7_relat_1(sK0,sK2) = X4
        | r2_hidden(sK4(X4,k7_relat_1(sK0,sK2)),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f344,plain,
    ( k1_funct_1(sK0,sK4(k7_relat_1(sK1,sK2),k7_relat_1(sK0,sK2))) != k1_funct_1(k7_relat_1(sK0,sK2),sK4(k7_relat_1(sK1,sK2),k7_relat_1(sK0,sK2)))
    | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | k1_relat_1(k7_relat_1(sK0,sK2)) != k1_relat_1(k7_relat_1(sK1,sK2))
    | ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_funct_1(k7_relat_1(sK1,sK2))
    | ~ v1_relat_1(k7_relat_1(sK1,sK2))
    | spl5_1
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(superposition,[],[f39,f332])).

fof(f332,plain,
    ( k1_funct_1(sK0,sK4(k7_relat_1(sK1,sK2),k7_relat_1(sK0,sK2))) = k1_funct_1(k7_relat_1(sK1,sK2),sK4(k7_relat_1(sK1,sK2),k7_relat_1(sK0,sK2)))
    | spl5_1
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f331,f309])).

fof(f309,plain,
    ( k1_funct_1(sK0,sK4(k7_relat_1(sK1,sK2),k7_relat_1(sK0,sK2))) = k1_funct_1(sK1,sK4(k7_relat_1(sK1,sK2),k7_relat_1(sK0,sK2)))
    | spl5_1
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(resolution,[],[f308,f62])).

fof(f62,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK2)
        | k1_funct_1(sK0,X4) = k1_funct_1(sK1,X4) )
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl5_4
  <=> ! [X4] :
        ( k1_funct_1(sK0,X4) = k1_funct_1(sK1,X4)
        | ~ r2_hidden(X4,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f331,plain,
    ( k1_funct_1(sK1,sK4(k7_relat_1(sK1,sK2),k7_relat_1(sK0,sK2))) = k1_funct_1(k7_relat_1(sK1,sK2),sK4(k7_relat_1(sK1,sK2),k7_relat_1(sK0,sK2)))
    | spl5_1
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f325,f31])).

fof(f325,plain,
    ( k1_funct_1(sK1,sK4(k7_relat_1(sK1,sK2),k7_relat_1(sK0,sK2))) = k1_funct_1(k7_relat_1(sK1,sK2),sK4(k7_relat_1(sK1,sK2),k7_relat_1(sK0,sK2)))
    | ~ v1_relat_1(sK1)
    | spl5_1
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(resolution,[],[f310,f32])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | X0 = X1
      | k1_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
            & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X1) = k1_relat_1(X0) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

fof(f180,plain,(
    spl5_7 ),
    inference(avatar_contradiction_clause,[],[f179])).

fof(f179,plain,
    ( $false
    | spl5_7 ),
    inference(subsumption_resolution,[],[f178,f31])).

fof(f178,plain,
    ( ~ v1_relat_1(sK1)
    | spl5_7 ),
    inference(subsumption_resolution,[],[f177,f32])).

fof(f177,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl5_7 ),
    inference(resolution,[],[f172,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f172,plain,
    ( ~ v1_funct_1(k7_relat_1(sK1,sK2))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f170])).

fof(f125,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | spl5_5 ),
    inference(subsumption_resolution,[],[f123,f29])).

fof(f123,plain,
    ( ~ v1_relat_1(sK0)
    | spl5_5 ),
    inference(subsumption_resolution,[],[f122,f30])).

fof(f122,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl5_5 ),
    inference(resolution,[],[f117,f44])).

fof(f117,plain,
    ( ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f115])).

fof(f121,plain,
    ( ~ spl5_5
    | spl5_6 ),
    inference(avatar_split_clause,[],[f113,f119,f115])).

fof(f113,plain,(
    ! [X4] :
      ( sK2 != k1_relat_1(X4)
      | r2_hidden(sK4(X4,k7_relat_1(sK0,sK2)),sK2)
      | k7_relat_1(sK0,sK2) = X4
      | ~ v1_funct_1(k7_relat_1(sK0,sK2))
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4) ) ),
    inference(inner_rewriting,[],[f110])).

fof(f110,plain,(
    ! [X4] :
      ( sK2 != k1_relat_1(X4)
      | r2_hidden(sK4(X4,k7_relat_1(sK0,sK2)),k1_relat_1(X4))
      | k7_relat_1(sK0,sK2) = X4
      | ~ v1_funct_1(k7_relat_1(sK0,sK2))
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4) ) ),
    inference(superposition,[],[f88,f70])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k3_xboole_0(X0,k1_relat_1(sK0))
      | r2_hidden(sK4(X1,k7_relat_1(sK0,X0)),k1_relat_1(X1))
      | k7_relat_1(sK0,X0) = X1
      | ~ v1_funct_1(k7_relat_1(sK0,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f79,f40])).

fof(f79,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(k1_relat_1(sK0),X2) != k1_relat_1(X3)
      | r2_hidden(sK4(X3,k7_relat_1(sK0,X2)),k1_relat_1(X3))
      | k7_relat_1(sK0,X2) = X3
      | ~ v1_funct_1(k7_relat_1(sK0,X2))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(subsumption_resolution,[],[f77,f66])).

fof(f77,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(k1_relat_1(sK0),X2) != k1_relat_1(X3)
      | r2_hidden(sK4(X3,k7_relat_1(sK0,X2)),k1_relat_1(X3))
      | k7_relat_1(sK0,X2) = X3
      | ~ v1_funct_1(k7_relat_1(sK0,X2))
      | ~ v1_relat_1(k7_relat_1(sK0,X2))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f38,f64])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k1_relat_1(X0)
      | r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | X0 = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f63,plain,
    ( spl5_1
    | spl5_4 ),
    inference(avatar_split_clause,[],[f35,f61,f47])).

fof(f35,plain,(
    ! [X4] :
      ( k1_funct_1(sK0,X4) = k1_funct_1(sK1,X4)
      | ~ r2_hidden(X4,sK2)
      | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f59,plain,
    ( ~ spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f36,f56,f47])).

fof(f36,plain,
    ( r2_hidden(sK3,sK2)
    | k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f54,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f37,f51,f47])).

fof(f37,plain,
    ( k1_funct_1(sK0,sK3) != k1_funct_1(sK1,sK3)
    | k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

%------------------------------------------------------------------------------
