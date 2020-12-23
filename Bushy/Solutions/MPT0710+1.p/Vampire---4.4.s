%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t165_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:19 EDT 2019

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 581 expanded)
%              Number of leaves         :   33 ( 223 expanded)
%              Depth                    :   16
%              Number of atoms          :  577 (4460 expanded)
%              Number of equality atoms :  158 (1469 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2336,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f110,f117,f189,f204,f239,f242,f267,f294,f297,f331,f344,f704,f709,f712,f1639,f1640,f1835,f1840,f2335])).

fof(f2335,plain,
    ( ~ spl6_41
    | ~ spl6_43
    | ~ spl6_47
    | ~ spl6_49
    | spl6_0
    | ~ spl6_322
    | ~ spl6_324 ),
    inference(avatar_split_clause,[],[f2334,f1838,f1833,f112,f274,f271,f262,f259])).

fof(f259,plain,
    ( spl6_41
  <=> ~ v1_relat_1(k7_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f262,plain,
    ( spl6_43
  <=> ~ v1_funct_1(k7_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f271,plain,
    ( spl6_47
  <=> ~ v1_relat_1(k7_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f274,plain,
    ( spl6_49
  <=> ~ v1_funct_1(k7_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f112,plain,
    ( spl6_0
  <=> k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f1833,plain,
    ( spl6_322
  <=> k1_funct_1(sK0,sK4(k7_relat_1(sK0,sK2),k7_relat_1(sK1,sK2))) = k1_funct_1(k7_relat_1(sK0,sK2),sK4(k7_relat_1(sK0,sK2),k7_relat_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_322])])).

fof(f1838,plain,
    ( spl6_324
  <=> k1_funct_1(sK0,sK4(k7_relat_1(sK0,sK2),k7_relat_1(sK1,sK2))) = k1_funct_1(k7_relat_1(sK1,sK2),sK4(k7_relat_1(sK0,sK2),k7_relat_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_324])])).

fof(f2334,plain,
    ( k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | ~ v1_funct_1(k7_relat_1(sK1,sK2))
    | ~ v1_relat_1(k7_relat_1(sK1,sK2))
    | ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ spl6_322
    | ~ spl6_324 ),
    inference(trivial_inequality_removal,[],[f2333])).

fof(f2333,plain,
    ( sK2 != sK2
    | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | ~ v1_funct_1(k7_relat_1(sK1,sK2))
    | ~ v1_relat_1(k7_relat_1(sK1,sK2))
    | ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ spl6_322
    | ~ spl6_324 ),
    inference(forward_demodulation,[],[f2332,f210])).

fof(f210,plain,(
    k1_relat_1(k7_relat_1(sK0,sK2)) = sK2 ),
    inference(superposition,[],[f126,f122])).

fof(f122,plain,(
    k3_xboole_0(sK2,k1_relat_1(sK0)) = sK2 ),
    inference(resolution,[],[f69,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t165_funct_1.p',t28_xboole_1)).

fof(f69,plain,(
    r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f54,f58,f57,f56,f55])).

fof(f55,plain,
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
                    ( k1_funct_1(sK0,X3) != k1_funct_1(X1,X3)
                    & r2_hidden(X3,X2) )
                | k7_relat_1(sK0,X2) != k7_relat_1(X1,X2) )
              & ( ! [X4] :
                    ( k1_funct_1(sK0,X4) = k1_funct_1(X1,X4)
                    | ~ r2_hidden(X4,X2) )
                | k7_relat_1(sK0,X2) = k7_relat_1(X1,X2) )
              & r1_tarski(X2,k1_relat_1(X1))
              & r1_tarski(X2,k1_relat_1(sK0)) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
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
     => ( ? [X2] :
            ( ( ? [X3] :
                  ( k1_funct_1(sK1,X3) != k1_funct_1(X0,X3)
                  & r2_hidden(X3,X2) )
              | k7_relat_1(sK1,X2) != k7_relat_1(X0,X2) )
            & ( ! [X4] :
                  ( k1_funct_1(sK1,X4) = k1_funct_1(X0,X4)
                  | ~ r2_hidden(X4,X2) )
              | k7_relat_1(sK1,X2) = k7_relat_1(X0,X2) )
            & r1_tarski(X2,k1_relat_1(sK1))
            & r1_tarski(X2,k1_relat_1(X0)) )
        & v1_funct_1(sK1)
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1] :
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
     => ( ( ? [X3] :
              ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
              & r2_hidden(X3,sK2) )
          | k7_relat_1(X0,sK2) != k7_relat_1(X1,sK2) )
        & ( ! [X4] :
              ( k1_funct_1(X0,X4) = k1_funct_1(X1,X4)
              | ~ r2_hidden(X4,sK2) )
          | k7_relat_1(X0,sK2) = k7_relat_1(X1,sK2) )
        & r1_tarski(sK2,k1_relat_1(X1))
        & r1_tarski(sK2,k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
          & r2_hidden(X3,X2) )
     => ( k1_funct_1(X0,sK3) != k1_funct_1(X1,sK3)
        & r2_hidden(sK3,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
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
    inference(rectify,[],[f53])).

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
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
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/funct_1__t165_funct_1.p',t165_funct_1)).

fof(f126,plain,(
    ! [X1] : k1_relat_1(k7_relat_1(sK0,X1)) = k3_xboole_0(X1,k1_relat_1(sK0)) ),
    inference(superposition,[],[f118,f82])).

fof(f82,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t165_funct_1.p',commutativity_k3_xboole_0)).

fof(f118,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK0,X0)) = k3_xboole_0(k1_relat_1(sK0),X0) ),
    inference(resolution,[],[f65,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t165_funct_1.p',t90_relat_1)).

fof(f65,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f2332,plain,
    ( k1_relat_1(k7_relat_1(sK0,sK2)) != sK2
    | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | ~ v1_funct_1(k7_relat_1(sK1,sK2))
    | ~ v1_relat_1(k7_relat_1(sK1,sK2))
    | ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ spl6_322
    | ~ spl6_324 ),
    inference(forward_demodulation,[],[f2331,f231])).

fof(f231,plain,(
    k1_relat_1(k7_relat_1(sK1,sK2)) = sK2 ),
    inference(superposition,[],[f134,f123])).

fof(f123,plain,(
    k3_xboole_0(sK2,k1_relat_1(sK1)) = sK2 ),
    inference(resolution,[],[f70,f85])).

fof(f70,plain,(
    r1_tarski(sK2,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f59])).

fof(f134,plain,(
    ! [X1] : k1_relat_1(k7_relat_1(sK1,X1)) = k3_xboole_0(X1,k1_relat_1(sK1)) ),
    inference(superposition,[],[f120,f82])).

fof(f120,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0) ),
    inference(resolution,[],[f67,f84])).

fof(f67,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f2331,plain,
    ( k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | k1_relat_1(k7_relat_1(sK0,sK2)) != k1_relat_1(k7_relat_1(sK1,sK2))
    | ~ v1_funct_1(k7_relat_1(sK1,sK2))
    | ~ v1_relat_1(k7_relat_1(sK1,sK2))
    | ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ spl6_322
    | ~ spl6_324 ),
    inference(trivial_inequality_removal,[],[f2330])).

fof(f2330,plain,
    ( k1_funct_1(sK0,sK4(k7_relat_1(sK0,sK2),k7_relat_1(sK1,sK2))) != k1_funct_1(sK0,sK4(k7_relat_1(sK0,sK2),k7_relat_1(sK1,sK2)))
    | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | k1_relat_1(k7_relat_1(sK0,sK2)) != k1_relat_1(k7_relat_1(sK1,sK2))
    | ~ v1_funct_1(k7_relat_1(sK1,sK2))
    | ~ v1_relat_1(k7_relat_1(sK1,sK2))
    | ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ spl6_322
    | ~ spl6_324 ),
    inference(forward_demodulation,[],[f2329,f1834])).

fof(f1834,plain,
    ( k1_funct_1(sK0,sK4(k7_relat_1(sK0,sK2),k7_relat_1(sK1,sK2))) = k1_funct_1(k7_relat_1(sK0,sK2),sK4(k7_relat_1(sK0,sK2),k7_relat_1(sK1,sK2)))
    | ~ spl6_322 ),
    inference(avatar_component_clause,[],[f1833])).

fof(f2329,plain,
    ( k1_funct_1(sK0,sK4(k7_relat_1(sK0,sK2),k7_relat_1(sK1,sK2))) != k1_funct_1(k7_relat_1(sK0,sK2),sK4(k7_relat_1(sK0,sK2),k7_relat_1(sK1,sK2)))
    | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | k1_relat_1(k7_relat_1(sK0,sK2)) != k1_relat_1(k7_relat_1(sK1,sK2))
    | ~ v1_funct_1(k7_relat_1(sK1,sK2))
    | ~ v1_relat_1(k7_relat_1(sK1,sK2))
    | ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ spl6_324 ),
    inference(superposition,[],[f79,f1839])).

fof(f1839,plain,
    ( k1_funct_1(sK0,sK4(k7_relat_1(sK0,sK2),k7_relat_1(sK1,sK2))) = k1_funct_1(k7_relat_1(sK1,sK2),sK4(k7_relat_1(sK0,sK2),k7_relat_1(sK1,sK2)))
    | ~ spl6_324 ),
    inference(avatar_component_clause,[],[f1838])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | X0 = X1
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
            & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f60])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t165_funct_1.p',t9_funct_1)).

fof(f1840,plain,
    ( ~ spl6_37
    | spl6_324
    | ~ spl6_180
    | ~ spl6_254 ),
    inference(avatar_split_clause,[],[f1836,f1122,f661,f1838,f222])).

fof(f222,plain,
    ( spl6_37
  <=> ~ v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f661,plain,
    ( spl6_180
  <=> k1_funct_1(sK0,sK4(k7_relat_1(sK0,sK2),k7_relat_1(sK1,sK2))) = k1_funct_1(sK1,sK4(k7_relat_1(sK0,sK2),k7_relat_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_180])])).

fof(f1122,plain,
    ( spl6_254
  <=> ! [X6] :
        ( k1_funct_1(X6,sK4(k7_relat_1(sK0,sK2),k7_relat_1(sK1,sK2))) = k1_funct_1(k7_relat_1(X6,sK2),sK4(k7_relat_1(sK0,sK2),k7_relat_1(sK1,sK2)))
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_254])])).

fof(f1836,plain,
    ( k1_funct_1(sK0,sK4(k7_relat_1(sK0,sK2),k7_relat_1(sK1,sK2))) = k1_funct_1(k7_relat_1(sK1,sK2),sK4(k7_relat_1(sK0,sK2),k7_relat_1(sK1,sK2)))
    | ~ v1_relat_1(sK1)
    | ~ spl6_180
    | ~ spl6_254 ),
    inference(forward_demodulation,[],[f1823,f662])).

fof(f662,plain,
    ( k1_funct_1(sK0,sK4(k7_relat_1(sK0,sK2),k7_relat_1(sK1,sK2))) = k1_funct_1(sK1,sK4(k7_relat_1(sK0,sK2),k7_relat_1(sK1,sK2)))
    | ~ spl6_180 ),
    inference(avatar_component_clause,[],[f661])).

fof(f1823,plain,
    ( ~ v1_relat_1(sK1)
    | k1_funct_1(sK1,sK4(k7_relat_1(sK0,sK2),k7_relat_1(sK1,sK2))) = k1_funct_1(k7_relat_1(sK1,sK2),sK4(k7_relat_1(sK0,sK2),k7_relat_1(sK1,sK2)))
    | ~ spl6_254 ),
    inference(resolution,[],[f1123,f68])).

fof(f68,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f1123,plain,
    ( ! [X6] :
        ( ~ v1_funct_1(X6)
        | ~ v1_relat_1(X6)
        | k1_funct_1(X6,sK4(k7_relat_1(sK0,sK2),k7_relat_1(sK1,sK2))) = k1_funct_1(k7_relat_1(X6,sK2),sK4(k7_relat_1(sK0,sK2),k7_relat_1(sK1,sK2))) )
    | ~ spl6_254 ),
    inference(avatar_component_clause,[],[f1122])).

fof(f1835,plain,
    ( spl6_322
    | ~ spl6_21
    | ~ spl6_254 ),
    inference(avatar_split_clause,[],[f1822,f1122,f170,f1833])).

fof(f170,plain,
    ( spl6_21
  <=> ~ v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f1822,plain,
    ( ~ v1_relat_1(sK0)
    | k1_funct_1(sK0,sK4(k7_relat_1(sK0,sK2),k7_relat_1(sK1,sK2))) = k1_funct_1(k7_relat_1(sK0,sK2),sK4(k7_relat_1(sK0,sK2),k7_relat_1(sK1,sK2)))
    | ~ spl6_254 ),
    inference(resolution,[],[f1123,f66])).

fof(f66,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f1640,plain,
    ( spl6_180
    | spl6_0
    | ~ spl6_49
    | ~ spl6_47
    | ~ spl6_6
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f1635,f265,f115,f271,f274,f112,f661])).

fof(f115,plain,
    ( spl6_6
  <=> ! [X4] :
        ( k1_funct_1(sK0,X4) = k1_funct_1(sK1,X4)
        | ~ r2_hidden(X4,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f265,plain,
    ( spl6_44
  <=> ! [X0] :
        ( k1_relat_1(X0) != sK2
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k7_relat_1(sK0,sK2) = X0
        | r2_hidden(sK4(k7_relat_1(sK0,sK2),X0),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f1635,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK2))
    | ~ v1_funct_1(k7_relat_1(sK1,sK2))
    | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | k1_funct_1(sK0,sK4(k7_relat_1(sK0,sK2),k7_relat_1(sK1,sK2))) = k1_funct_1(sK1,sK4(k7_relat_1(sK0,sK2),k7_relat_1(sK1,sK2)))
    | ~ spl6_6
    | ~ spl6_44 ),
    inference(trivial_inequality_removal,[],[f1633])).

fof(f1633,plain,
    ( sK2 != sK2
    | ~ v1_relat_1(k7_relat_1(sK1,sK2))
    | ~ v1_funct_1(k7_relat_1(sK1,sK2))
    | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | k1_funct_1(sK0,sK4(k7_relat_1(sK0,sK2),k7_relat_1(sK1,sK2))) = k1_funct_1(sK1,sK4(k7_relat_1(sK0,sK2),k7_relat_1(sK1,sK2)))
    | ~ spl6_6
    | ~ spl6_44 ),
    inference(superposition,[],[f719,f231])).

fof(f719,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK2
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k7_relat_1(sK0,sK2) = X0
        | k1_funct_1(sK0,sK4(k7_relat_1(sK0,sK2),X0)) = k1_funct_1(sK1,sK4(k7_relat_1(sK0,sK2),X0)) )
    | ~ spl6_6
    | ~ spl6_44 ),
    inference(resolution,[],[f116,f266])).

fof(f266,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(k7_relat_1(sK0,sK2),X0),sK2)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k7_relat_1(sK0,sK2) = X0
        | k1_relat_1(X0) != sK2 )
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f265])).

fof(f116,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK2)
        | k1_funct_1(sK0,X4) = k1_funct_1(sK1,X4) )
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f115])).

fof(f1639,plain,
    ( spl6_254
    | ~ spl6_47
    | spl6_0
    | ~ spl6_49
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f1636,f265,f274,f112,f271,f1122])).

fof(f1636,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(k7_relat_1(sK1,sK2))
        | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
        | ~ v1_relat_1(k7_relat_1(sK1,sK2))
        | k1_funct_1(X1,sK4(k7_relat_1(sK0,sK2),k7_relat_1(sK1,sK2))) = k1_funct_1(k7_relat_1(X1,sK2),sK4(k7_relat_1(sK0,sK2),k7_relat_1(sK1,sK2)))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl6_44 ),
    inference(trivial_inequality_removal,[],[f1630])).

fof(f1630,plain,
    ( ! [X1] :
        ( sK2 != sK2
        | ~ v1_funct_1(k7_relat_1(sK1,sK2))
        | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
        | ~ v1_relat_1(k7_relat_1(sK1,sK2))
        | k1_funct_1(X1,sK4(k7_relat_1(sK0,sK2),k7_relat_1(sK1,sK2))) = k1_funct_1(k7_relat_1(X1,sK2),sK4(k7_relat_1(sK0,sK2),k7_relat_1(sK1,sK2)))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl6_44 ),
    inference(superposition,[],[f425,f231])).

fof(f425,plain,
    ( ! [X2,X1] :
        ( k1_relat_1(X1) != sK2
        | ~ v1_funct_1(X1)
        | k7_relat_1(sK0,sK2) = X1
        | ~ v1_relat_1(X1)
        | k1_funct_1(X2,sK4(k7_relat_1(sK0,sK2),X1)) = k1_funct_1(k7_relat_1(X2,sK2),sK4(k7_relat_1(sK0,sK2),X1))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | ~ spl6_44 ),
    inference(resolution,[],[f266,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,X1)
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t165_funct_1.p',t72_funct_1)).

fof(f712,plain,
    ( spl6_3
    | ~ spl6_186
    | ~ spl6_188 ),
    inference(avatar_contradiction_clause,[],[f711])).

fof(f711,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_186
    | ~ spl6_188 ),
    inference(subsumption_resolution,[],[f105,f710])).

fof(f710,plain,
    ( k1_funct_1(sK0,sK3) = k1_funct_1(sK1,sK3)
    | ~ spl6_186
    | ~ spl6_188 ),
    inference(forward_demodulation,[],[f708,f703])).

fof(f703,plain,
    ( k1_funct_1(sK0,sK3) = k1_funct_1(k7_relat_1(sK0,sK2),sK3)
    | ~ spl6_186 ),
    inference(avatar_component_clause,[],[f702])).

fof(f702,plain,
    ( spl6_186
  <=> k1_funct_1(sK0,sK3) = k1_funct_1(k7_relat_1(sK0,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_186])])).

fof(f708,plain,
    ( k1_funct_1(sK1,sK3) = k1_funct_1(k7_relat_1(sK0,sK2),sK3)
    | ~ spl6_188 ),
    inference(avatar_component_clause,[],[f707])).

fof(f707,plain,
    ( spl6_188
  <=> k1_funct_1(sK1,sK3) = k1_funct_1(k7_relat_1(sK0,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_188])])).

fof(f105,plain,
    ( k1_funct_1(sK0,sK3) != k1_funct_1(sK1,sK3)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl6_3
  <=> k1_funct_1(sK0,sK3) != k1_funct_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f709,plain,
    ( ~ spl6_37
    | spl6_188
    | ~ spl6_0
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f705,f108,f112,f707,f222])).

fof(f108,plain,
    ( spl6_4
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f705,plain,
    ( k1_funct_1(sK1,sK3) = k1_funct_1(k7_relat_1(sK0,sK2),sK3)
    | ~ v1_relat_1(sK1)
    | ~ spl6_0
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f692,f113])).

fof(f113,plain,
    ( k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f112])).

fof(f692,plain,
    ( k1_funct_1(sK1,sK3) = k1_funct_1(k7_relat_1(sK1,sK2),sK3)
    | ~ v1_relat_1(sK1)
    | ~ spl6_4 ),
    inference(resolution,[],[f665,f68])).

fof(f665,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | k1_funct_1(X0,sK3) = k1_funct_1(k7_relat_1(X0,sK2),sK3)
        | ~ v1_relat_1(X0) )
    | ~ spl6_4 ),
    inference(resolution,[],[f109,f95])).

fof(f109,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f704,plain,
    ( ~ spl6_21
    | spl6_186
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f691,f108,f702,f170])).

fof(f691,plain,
    ( k1_funct_1(sK0,sK3) = k1_funct_1(k7_relat_1(sK0,sK2),sK3)
    | ~ v1_relat_1(sK0)
    | ~ spl6_4 ),
    inference(resolution,[],[f665,f66])).

fof(f344,plain,
    ( ~ spl6_37
    | ~ spl6_39
    | spl6_49 ),
    inference(avatar_split_clause,[],[f343,f274,f225,f222])).

fof(f225,plain,
    ( spl6_39
  <=> ~ v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f343,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl6_49 ),
    inference(resolution,[],[f275,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t165_funct_1.p',fc8_funct_1)).

fof(f275,plain,
    ( ~ v1_funct_1(k7_relat_1(sK1,sK2))
    | ~ spl6_49 ),
    inference(avatar_component_clause,[],[f274])).

fof(f331,plain,(
    spl6_47 ),
    inference(avatar_contradiction_clause,[],[f330])).

fof(f330,plain,
    ( $false
    | ~ spl6_47 ),
    inference(subsumption_resolution,[],[f67,f298])).

fof(f298,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl6_47 ),
    inference(resolution,[],[f272,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t165_funct_1.p',dt_k7_relat_1)).

fof(f272,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK2))
    | ~ spl6_47 ),
    inference(avatar_component_clause,[],[f271])).

fof(f297,plain,
    ( ~ spl6_21
    | ~ spl6_23
    | spl6_43 ),
    inference(avatar_split_clause,[],[f296,f262,f173,f170])).

fof(f173,plain,
    ( spl6_23
  <=> ~ v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f296,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl6_43 ),
    inference(resolution,[],[f263,f90])).

fof(f263,plain,
    ( ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f262])).

fof(f294,plain,(
    spl6_41 ),
    inference(avatar_contradiction_clause,[],[f293])).

fof(f293,plain,
    ( $false
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f65,f280])).

fof(f280,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl6_41 ),
    inference(resolution,[],[f260,f83])).

fof(f260,plain,
    ( ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f259])).

fof(f267,plain,
    ( ~ spl6_41
    | ~ spl6_43
    | spl6_44 ),
    inference(avatar_split_clause,[],[f257,f265,f262,f259])).

fof(f257,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != sK2
      | r2_hidden(sK4(k7_relat_1(sK0,sK2),X0),sK2)
      | k7_relat_1(sK0,sK2) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(k7_relat_1(sK0,sK2))
      | ~ v1_relat_1(k7_relat_1(sK0,sK2)) ) ),
    inference(forward_demodulation,[],[f256,f210])).

fof(f256,plain,(
    ! [X0] :
      ( r2_hidden(sK4(k7_relat_1(sK0,sK2),X0),sK2)
      | k7_relat_1(sK0,sK2) = X0
      | k1_relat_1(X0) != k1_relat_1(k7_relat_1(sK0,sK2))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(k7_relat_1(sK0,sK2))
      | ~ v1_relat_1(k7_relat_1(sK0,sK2)) ) ),
    inference(superposition,[],[f78,f210])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | X0 = X1
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f242,plain,(
    spl6_39 ),
    inference(avatar_contradiction_clause,[],[f241])).

fof(f241,plain,
    ( $false
    | ~ spl6_39 ),
    inference(subsumption_resolution,[],[f68,f226])).

fof(f226,plain,
    ( ~ v1_funct_1(sK1)
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f225])).

fof(f239,plain,(
    spl6_37 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | ~ spl6_37 ),
    inference(subsumption_resolution,[],[f67,f223])).

fof(f223,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f222])).

fof(f204,plain,(
    spl6_23 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f66,f174])).

fof(f174,plain,
    ( ~ v1_funct_1(sK0)
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f173])).

fof(f189,plain,(
    spl6_21 ),
    inference(avatar_contradiction_clause,[],[f188])).

fof(f188,plain,
    ( $false
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f65,f171])).

fof(f171,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f170])).

fof(f117,plain,
    ( spl6_0
    | spl6_6 ),
    inference(avatar_split_clause,[],[f71,f115,f112])).

fof(f71,plain,(
    ! [X4] :
      ( k1_funct_1(sK0,X4) = k1_funct_1(sK1,X4)
      | ~ r2_hidden(X4,sK2)
      | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f110,plain,
    ( ~ spl6_1
    | spl6_4 ),
    inference(avatar_split_clause,[],[f72,f108,f101])).

fof(f101,plain,
    ( spl6_1
  <=> k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f72,plain,
    ( r2_hidden(sK3,sK2)
    | k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f106,plain,
    ( ~ spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f73,f104,f101])).

fof(f73,plain,
    ( k1_funct_1(sK0,sK3) != k1_funct_1(sK1,sK3)
    | k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f59])).
%------------------------------------------------------------------------------
