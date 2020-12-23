%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : wellord1__t49_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:14 EDT 2019

% Result     : Theorem 164.63s
% Output     : Refutation 164.63s
% Verified   : 
% Statistics : Number of formulae       :  192 (5233 expanded)
%              Number of leaves         :   18 (1898 expanded)
%              Depth                    :   52
%              Number of atoms          : 1013 (40083 expanded)
%              Number of equality atoms :  190 (2086 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f136552,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1028,f136241,f136487])).

fof(f136487,plain,
    ( spl8_143
    | ~ spl8_144 ),
    inference(avatar_contradiction_clause,[],[f136486])).

fof(f136486,plain,
    ( $false
    | ~ spl8_143
    | ~ spl8_144 ),
    inference(subsumption_resolution,[],[f136485,f1006])).

fof(f1006,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | ~ spl8_143 ),
    inference(avatar_component_clause,[],[f1005])).

fof(f1005,plain,
    ( spl8_143
  <=> ~ r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),sK4(sK1,sK0,k2_funct_1(sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_143])])).

fof(f136485,plain,
    ( r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | ~ spl8_144 ),
    inference(forward_demodulation,[],[f136484,f2355])).

fof(f2355,plain,(
    k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2)))) = sK3(sK1,sK0,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f2354,f66])).

fof(f66,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( ~ r3_wellord1(sK1,sK0,k2_funct_1(sK2))
    & r3_wellord1(sK0,sK1,sK2)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f51,f50,f49])).

fof(f49,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r3_wellord1(X1,X0,k2_funct_1(X2))
                & r3_wellord1(X0,X1,X2)
                & v1_funct_1(X2)
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_wellord1(X1,sK0,k2_funct_1(X2))
              & r3_wellord1(sK0,X1,X2)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_wellord1(X1,X0,k2_funct_1(X2))
              & r3_wellord1(X0,X1,X2)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( ~ r3_wellord1(sK1,X0,k2_funct_1(X2))
            & r3_wellord1(X0,sK1,X2)
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r3_wellord1(X1,X0,k2_funct_1(X2))
          & r3_wellord1(X0,X1,X2)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ~ r3_wellord1(X1,X0,k2_funct_1(sK2))
        & r3_wellord1(X0,X1,sK2)
        & v1_funct_1(sK2)
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_wellord1(X1,X0,k2_funct_1(X2))
              & r3_wellord1(X0,X1,X2)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_wellord1(X1,X0,k2_funct_1(X2))
              & r3_wellord1(X0,X1,X2)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( r3_wellord1(X0,X1,X2)
                 => r3_wellord1(X1,X0,k2_funct_1(X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( r3_wellord1(X0,X1,X2)
               => r3_wellord1(X1,X0,k2_funct_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t49_wellord1.p',t49_wellord1)).

fof(f2354,plain,
    ( k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2)))) = sK3(sK1,sK0,k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f2353,f67])).

fof(f67,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f2353,plain,
    ( k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2)))) = sK3(sK1,sK0,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f2343,f687])).

fof(f687,plain,(
    v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f686,f64])).

fof(f64,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f686,plain,
    ( v2_funct_1(sK2)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f685,f65])).

fof(f65,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f685,plain,
    ( v2_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f684,f66])).

fof(f684,plain,
    ( v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f655,f67])).

fof(f655,plain,
    ( v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f68,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_wellord1(X0,X1,X2)
                  | ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X2,sK3(X0,X1,X2)),k1_funct_1(X2,sK4(X0,X1,X2))),X1)
                      | ~ r2_hidden(sK4(X0,X1,X2),k3_relat_1(X0))
                      | ~ r2_hidden(sK3(X0,X1,X2),k3_relat_1(X0))
                      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) )
                    & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,sK3(X0,X1,X2)),k1_funct_1(X2,sK4(X0,X1,X2))),X1)
                        & r2_hidden(sK4(X0,X1,X2),k3_relat_1(X0))
                        & r2_hidden(sK3(X0,X1,X2),k3_relat_1(X0)) )
                      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) ) )
                  | ~ v2_funct_1(X2)
                  | k2_relat_1(X2) != k3_relat_1(X1)
                  | k1_relat_1(X2) != k3_relat_1(X0) )
                & ( ( ! [X5,X6] :
                        ( ( r2_hidden(k4_tarski(X5,X6),X0)
                          | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X5),k1_funct_1(X2,X6)),X1)
                          | ~ r2_hidden(X6,k3_relat_1(X0))
                          | ~ r2_hidden(X5,k3_relat_1(X0)) )
                        & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X5),k1_funct_1(X2,X6)),X1)
                            & r2_hidden(X6,k3_relat_1(X0))
                            & r2_hidden(X5,k3_relat_1(X0)) )
                          | ~ r2_hidden(k4_tarski(X5,X6),X0) ) )
                    & v2_funct_1(X2)
                    & k2_relat_1(X2) = k3_relat_1(X1)
                    & k1_relat_1(X2) = k3_relat_1(X0) )
                  | ~ r3_wellord1(X0,X1,X2) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f55,f56])).

fof(f56,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
            | ~ r2_hidden(X4,k3_relat_1(X0))
            | ~ r2_hidden(X3,k3_relat_1(X0))
            | ~ r2_hidden(k4_tarski(X3,X4),X0) )
          & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
              & r2_hidden(X4,k3_relat_1(X0))
              & r2_hidden(X3,k3_relat_1(X0)) )
            | r2_hidden(k4_tarski(X3,X4),X0) ) )
     => ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X2,sK3(X0,X1,X2)),k1_funct_1(X2,sK4(X0,X1,X2))),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),k3_relat_1(X0))
          | ~ r2_hidden(sK3(X0,X1,X2),k3_relat_1(X0))
          | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) )
        & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,sK3(X0,X1,X2)),k1_funct_1(X2,sK4(X0,X1,X2))),X1)
            & r2_hidden(sK4(X0,X1,X2),k3_relat_1(X0))
            & r2_hidden(sK3(X0,X1,X2),k3_relat_1(X0)) )
          | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_wellord1(X0,X1,X2)
                  | ? [X3,X4] :
                      ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        | ~ r2_hidden(X4,k3_relat_1(X0))
                        | ~ r2_hidden(X3,k3_relat_1(X0))
                        | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                      & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                          & r2_hidden(X4,k3_relat_1(X0))
                          & r2_hidden(X3,k3_relat_1(X0)) )
                        | r2_hidden(k4_tarski(X3,X4),X0) ) )
                  | ~ v2_funct_1(X2)
                  | k2_relat_1(X2) != k3_relat_1(X1)
                  | k1_relat_1(X2) != k3_relat_1(X0) )
                & ( ( ! [X5,X6] :
                        ( ( r2_hidden(k4_tarski(X5,X6),X0)
                          | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X5),k1_funct_1(X2,X6)),X1)
                          | ~ r2_hidden(X6,k3_relat_1(X0))
                          | ~ r2_hidden(X5,k3_relat_1(X0)) )
                        & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X5),k1_funct_1(X2,X6)),X1)
                            & r2_hidden(X6,k3_relat_1(X0))
                            & r2_hidden(X5,k3_relat_1(X0)) )
                          | ~ r2_hidden(k4_tarski(X5,X6),X0) ) )
                    & v2_funct_1(X2)
                    & k2_relat_1(X2) = k3_relat_1(X1)
                    & k1_relat_1(X2) = k3_relat_1(X0) )
                  | ~ r3_wellord1(X0,X1,X2) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_wellord1(X0,X1,X2)
                  | ? [X3,X4] :
                      ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        | ~ r2_hidden(X4,k3_relat_1(X0))
                        | ~ r2_hidden(X3,k3_relat_1(X0))
                        | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                      & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                          & r2_hidden(X4,k3_relat_1(X0))
                          & r2_hidden(X3,k3_relat_1(X0)) )
                        | r2_hidden(k4_tarski(X3,X4),X0) ) )
                  | ~ v2_funct_1(X2)
                  | k2_relat_1(X2) != k3_relat_1(X1)
                  | k1_relat_1(X2) != k3_relat_1(X0) )
                & ( ( ! [X3,X4] :
                        ( ( r2_hidden(k4_tarski(X3,X4),X0)
                          | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                          | ~ r2_hidden(X4,k3_relat_1(X0))
                          | ~ r2_hidden(X3,k3_relat_1(X0)) )
                        & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                            & r2_hidden(X4,k3_relat_1(X0))
                            & r2_hidden(X3,k3_relat_1(X0)) )
                          | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                    & v2_funct_1(X2)
                    & k2_relat_1(X2) = k3_relat_1(X1)
                    & k1_relat_1(X2) = k3_relat_1(X0) )
                  | ~ r3_wellord1(X0,X1,X2) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_wellord1(X0,X1,X2)
                  | ? [X3,X4] :
                      ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        | ~ r2_hidden(X4,k3_relat_1(X0))
                        | ~ r2_hidden(X3,k3_relat_1(X0))
                        | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                      & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                          & r2_hidden(X4,k3_relat_1(X0))
                          & r2_hidden(X3,k3_relat_1(X0)) )
                        | r2_hidden(k4_tarski(X3,X4),X0) ) )
                  | ~ v2_funct_1(X2)
                  | k2_relat_1(X2) != k3_relat_1(X1)
                  | k1_relat_1(X2) != k3_relat_1(X0) )
                & ( ( ! [X3,X4] :
                        ( ( r2_hidden(k4_tarski(X3,X4),X0)
                          | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                          | ~ r2_hidden(X4,k3_relat_1(X0))
                          | ~ r2_hidden(X3,k3_relat_1(X0)) )
                        & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                            & r2_hidden(X4,k3_relat_1(X0))
                            & r2_hidden(X3,k3_relat_1(X0)) )
                          | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                    & v2_funct_1(X2)
                    & k2_relat_1(X2) = k3_relat_1(X1)
                    & k1_relat_1(X2) = k3_relat_1(X0) )
                  | ~ r3_wellord1(X0,X1,X2) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_wellord1(X0,X1,X2)
              <=> ( ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                    <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        & r2_hidden(X4,k3_relat_1(X0))
                        & r2_hidden(X3,k3_relat_1(X0)) ) )
                  & v2_funct_1(X2)
                  & k2_relat_1(X2) = k3_relat_1(X1)
                  & k1_relat_1(X2) = k3_relat_1(X0) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_wellord1(X0,X1,X2)
              <=> ( ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                    <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        & r2_hidden(X4,k3_relat_1(X0))
                        & r2_hidden(X3,k3_relat_1(X0)) ) )
                  & v2_funct_1(X2)
                  & k2_relat_1(X2) = k3_relat_1(X1)
                  & k1_relat_1(X2) = k3_relat_1(X0) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( r3_wellord1(X0,X1,X2)
              <=> ( ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                    <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        & r2_hidden(X4,k3_relat_1(X0))
                        & r2_hidden(X3,k3_relat_1(X0)) ) )
                  & v2_funct_1(X2)
                  & k2_relat_1(X2) = k3_relat_1(X1)
                  & k1_relat_1(X2) = k3_relat_1(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t49_wellord1.p',d7_wellord1)).

fof(f68,plain,(
    r3_wellord1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f2343,plain,
    ( k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2)))) = sK3(sK1,sK0,k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f983,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
        & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 )
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
        & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 )
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k2_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
          & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t49_wellord1.p',t57_funct_1)).

fof(f983,plain,(
    r2_hidden(sK3(sK1,sK0,k2_funct_1(sK2)),k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f982,f713])).

fof(f713,plain,(
    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f712,f66])).

fof(f712,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f627,f687])).

fof(f627,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f67,f70])).

fof(f70,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t49_wellord1.p',t55_funct_1)).

fof(f982,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | r2_hidden(sK3(sK1,sK0,k2_funct_1(sK2)),k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f981,f667])).

fof(f667,plain,(
    k2_relat_1(sK2) = k3_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f666,f64])).

fof(f666,plain,
    ( k2_relat_1(sK2) = k3_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f665,f65])).

fof(f665,plain,
    ( k2_relat_1(sK2) = k3_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f664,f66])).

fof(f664,plain,
    ( k2_relat_1(sK2) = k3_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f654,f67])).

fof(f654,plain,
    ( k2_relat_1(sK2) = k3_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f68,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k3_relat_1(X1)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f981,plain,
    ( r2_hidden(sK3(sK1,sK0,k2_funct_1(sK2)),k2_relat_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f980,f711])).

fof(f711,plain,(
    k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f710,f66])).

fof(f710,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f628,f687])).

fof(f628,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f67,f71])).

fof(f71,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f980,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | r2_hidden(sK3(sK1,sK0,k2_funct_1(sK2)),k2_relat_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1) ),
    inference(forward_demodulation,[],[f979,f663])).

fof(f663,plain,(
    k1_relat_1(sK2) = k3_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f662,f64])).

fof(f662,plain,
    ( k1_relat_1(sK2) = k3_relat_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f661,f65])).

fof(f661,plain,
    ( k1_relat_1(sK2) = k3_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f660,f66])).

fof(f660,plain,
    ( k1_relat_1(sK2) = k3_relat_1(sK0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f653,f67])).

fof(f653,plain,
    ( k1_relat_1(sK2) = k3_relat_1(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f68,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k3_relat_1(X0)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f979,plain,
    ( r2_hidden(sK3(sK1,sK0,k2_funct_1(sK2)),k2_relat_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1) ),
    inference(forward_demodulation,[],[f978,f667])).

fof(f978,plain,
    ( r2_hidden(sK3(sK1,sK0,k2_funct_1(sK2)),k3_relat_1(sK1))
    | k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f977,f338])).

fof(f338,plain,(
    ! [X97,X96] :
      ( ~ r2_hidden(k4_tarski(X96,X97),sK1)
      | r2_hidden(X96,k3_relat_1(sK1)) ) ),
    inference(resolution,[],[f65,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t49_wellord1.p',t30_relat_1)).

fof(f977,plain,
    ( r2_hidden(sK3(sK1,sK0,k2_funct_1(sK2)),k3_relat_1(sK1))
    | r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f976,f65])).

fof(f976,plain,
    ( r2_hidden(sK3(sK1,sK0,k2_funct_1(sK2)),k3_relat_1(sK1))
    | r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f975,f64])).

fof(f975,plain,
    ( r2_hidden(sK3(sK1,sK0,k2_funct_1(sK2)),k3_relat_1(sK1))
    | r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f974,f553])).

fof(f553,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f483,f67])).

fof(f483,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f66,f72])).

fof(f72,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t49_wellord1.p',dt_k2_funct_1)).

fof(f974,plain,
    ( r2_hidden(sK3(sK1,sK0,k2_funct_1(sK2)),k3_relat_1(sK1))
    | r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f973,f554])).

fof(f554,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f484,f67])).

fof(f484,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f66,f73])).

fof(f73,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f973,plain,
    ( r2_hidden(sK3(sK1,sK0,k2_funct_1(sK2)),k3_relat_1(sK1))
    | r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f969,f709])).

fof(f709,plain,(
    v2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f708,f66])).

fof(f708,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f633,f687])).

fof(f633,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f67,f76])).

fof(f76,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t49_wellord1.p',fc6_funct_1)).

fof(f969,plain,
    ( r2_hidden(sK3(sK1,sK0,k2_funct_1(sK2)),k3_relat_1(sK1))
    | r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f69,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r3_wellord1(X0,X1,X2)
      | r2_hidden(sK3(X0,X1,X2),k3_relat_1(X0))
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
      | ~ v2_funct_1(X2)
      | k2_relat_1(X2) != k3_relat_1(X1)
      | k1_relat_1(X2) != k3_relat_1(X0)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f69,plain,(
    ~ r3_wellord1(sK1,sK0,k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f52])).

fof(f136484,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2)))),sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | ~ spl8_144 ),
    inference(forward_demodulation,[],[f136404,f2389])).

fof(f2389,plain,(
    k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2)))) = sK4(sK1,sK0,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f2388,f66])).

fof(f2388,plain,
    ( k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2)))) = sK4(sK1,sK0,k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f2387,f67])).

fof(f2387,plain,
    ( k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2)))) = sK4(sK1,sK0,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f2377,f687])).

fof(f2377,plain,
    ( k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2)))) = sK4(sK1,sK0,k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f994,f95])).

fof(f994,plain,(
    r2_hidden(sK4(sK1,sK0,k2_funct_1(sK2)),k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f993,f713])).

fof(f993,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | r2_hidden(sK4(sK1,sK0,k2_funct_1(sK2)),k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f992,f667])).

fof(f992,plain,
    ( r2_hidden(sK4(sK1,sK0,k2_funct_1(sK2)),k2_relat_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f991,f711])).

fof(f991,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | r2_hidden(sK4(sK1,sK0,k2_funct_1(sK2)),k2_relat_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1) ),
    inference(forward_demodulation,[],[f990,f663])).

fof(f990,plain,
    ( r2_hidden(sK4(sK1,sK0,k2_funct_1(sK2)),k2_relat_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1) ),
    inference(forward_demodulation,[],[f989,f667])).

fof(f989,plain,
    ( r2_hidden(sK4(sK1,sK0,k2_funct_1(sK2)),k3_relat_1(sK1))
    | k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f988,f339])).

fof(f339,plain,(
    ! [X99,X98] :
      ( ~ r2_hidden(k4_tarski(X99,X98),sK1)
      | r2_hidden(X98,k3_relat_1(sK1)) ) ),
    inference(resolution,[],[f65,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f988,plain,
    ( r2_hidden(sK4(sK1,sK0,k2_funct_1(sK2)),k3_relat_1(sK1))
    | r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f987,f65])).

fof(f987,plain,
    ( r2_hidden(sK4(sK1,sK0,k2_funct_1(sK2)),k3_relat_1(sK1))
    | r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f986,f64])).

fof(f986,plain,
    ( r2_hidden(sK4(sK1,sK0,k2_funct_1(sK2)),k3_relat_1(sK1))
    | r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f985,f553])).

fof(f985,plain,
    ( r2_hidden(sK4(sK1,sK0,k2_funct_1(sK2)),k3_relat_1(sK1))
    | r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f984,f554])).

fof(f984,plain,
    ( r2_hidden(sK4(sK1,sK0,k2_funct_1(sK2)),k3_relat_1(sK1))
    | r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f970,f709])).

fof(f970,plain,
    ( r2_hidden(sK4(sK1,sK0,k2_funct_1(sK2)),k3_relat_1(sK1))
    | r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f69,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r3_wellord1(X0,X1,X2)
      | r2_hidden(sK4(X0,X1,X2),k3_relat_1(X0))
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
      | ~ v2_funct_1(X2)
      | k2_relat_1(X2) != k3_relat_1(X1)
      | k1_relat_1(X2) != k3_relat_1(X0)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f136404,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2)))),k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2))))),sK1)
    | ~ spl8_144 ),
    inference(resolution,[],[f1015,f677])).

fof(f677,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),sK0)
      | r2_hidden(k4_tarski(k1_funct_1(sK2,X4),k1_funct_1(sK2,X5)),sK1) ) ),
    inference(subsumption_resolution,[],[f676,f64])).

fof(f676,plain,(
    ! [X4,X5] :
      ( r2_hidden(k4_tarski(k1_funct_1(sK2,X4),k1_funct_1(sK2,X5)),sK1)
      | ~ r2_hidden(k4_tarski(X4,X5),sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f675,f65])).

fof(f675,plain,(
    ! [X4,X5] :
      ( r2_hidden(k4_tarski(k1_funct_1(sK2,X4),k1_funct_1(sK2,X5)),sK1)
      | ~ r2_hidden(k4_tarski(X4,X5),sK0)
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f674,f66])).

fof(f674,plain,(
    ! [X4,X5] :
      ( r2_hidden(k4_tarski(k1_funct_1(sK2,X4),k1_funct_1(sK2,X5)),sK1)
      | ~ r2_hidden(k4_tarski(X4,X5),sK0)
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f658,f67])).

fof(f658,plain,(
    ! [X4,X5] :
      ( r2_hidden(k4_tarski(k1_funct_1(sK2,X4),k1_funct_1(sK2,X5)),sK1)
      | ~ r2_hidden(k4_tarski(X4,X5),sK0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f68,f82])).

fof(f82,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(k1_funct_1(X2,X5),k1_funct_1(X2,X6)),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f1015,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2)))),sK0)
    | ~ spl8_144 ),
    inference(avatar_component_clause,[],[f1014])).

fof(f1014,plain,
    ( spl8_144
  <=> r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_144])])).

fof(f136241,plain,(
    spl8_145 ),
    inference(avatar_contradiction_clause,[],[f136240])).

fof(f136240,plain,
    ( $false
    | ~ spl8_145 ),
    inference(subsumption_resolution,[],[f136239,f713])).

fof(f136239,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | ~ spl8_145 ),
    inference(forward_demodulation,[],[f136238,f667])).

fof(f136238,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1)
    | ~ spl8_145 ),
    inference(subsumption_resolution,[],[f136237,f711])).

fof(f136237,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1)
    | ~ spl8_145 ),
    inference(forward_demodulation,[],[f136236,f663])).

fof(f136236,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1)
    | ~ spl8_145 ),
    inference(subsumption_resolution,[],[f136235,f64])).

fof(f136235,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl8_145 ),
    inference(subsumption_resolution,[],[f136234,f553])).

fof(f136234,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK0)
    | ~ spl8_145 ),
    inference(subsumption_resolution,[],[f136233,f554])).

fof(f136233,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK0)
    | ~ spl8_145 ),
    inference(subsumption_resolution,[],[f136232,f709])).

fof(f136232,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK0)
    | ~ spl8_145 ),
    inference(subsumption_resolution,[],[f136231,f1012])).

fof(f1012,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2)))),sK0)
    | ~ spl8_145 ),
    inference(avatar_component_clause,[],[f1011])).

fof(f1011,plain,
    ( spl8_145
  <=> ~ r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_145])])).

fof(f136231,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2)))),sK0)
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK0)
    | ~ spl8_145 ),
    inference(subsumption_resolution,[],[f136230,f69])).

fof(f136230,plain,
    ( r3_wellord1(sK1,sK0,k2_funct_1(sK2))
    | r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2)))),sK0)
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK0)
    | ~ spl8_145 ),
    inference(subsumption_resolution,[],[f136229,f65])).

fof(f136229,plain,
    ( ~ v1_relat_1(sK1)
    | r3_wellord1(sK1,sK0,k2_funct_1(sK2))
    | r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2)))),sK0)
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK0)
    | ~ spl8_145 ),
    inference(subsumption_resolution,[],[f136226,f68])).

fof(f136226,plain,
    ( ~ r3_wellord1(sK0,sK1,sK2)
    | ~ v1_relat_1(sK1)
    | r3_wellord1(sK1,sK0,k2_funct_1(sK2))
    | r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2)))),sK0)
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK0)
    | ~ spl8_145 ),
    inference(duplicate_literal_removal,[],[f136218])).

fof(f136218,plain,
    ( ~ r3_wellord1(sK0,sK1,sK2)
    | ~ v1_relat_1(sK1)
    | r3_wellord1(sK1,sK0,k2_funct_1(sK2))
    | r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2)))),sK0)
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl8_145 ),
    inference(resolution,[],[f43800,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r3_wellord1(X0,X1,X2)
      | r2_hidden(k4_tarski(k1_funct_1(X2,sK3(X0,X1,X2)),k1_funct_1(X2,sK4(X0,X1,X2))),X1)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
      | ~ v2_funct_1(X2)
      | k2_relat_1(X2) != k3_relat_1(X1)
      | k1_relat_1(X2) != k3_relat_1(X0)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f43800,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),sK4(sK1,sK0,k2_funct_1(sK2))),X0)
        | ~ r3_wellord1(sK0,X0,sK2)
        | ~ v1_relat_1(X0) )
    | ~ spl8_145 ),
    inference(forward_demodulation,[],[f43799,f2389])).

fof(f43799,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2))))),X0)
        | ~ r3_wellord1(sK0,X0,sK2)
        | ~ v1_relat_1(X0) )
    | ~ spl8_145 ),
    inference(subsumption_resolution,[],[f43798,f687])).

fof(f43798,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2))))),X0)
        | ~ r3_wellord1(sK0,X0,sK2)
        | ~ v1_relat_1(X0)
        | ~ v2_funct_1(sK2) )
    | ~ spl8_145 ),
    inference(subsumption_resolution,[],[f43797,f983])).

fof(f43797,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2))))),X0)
        | ~ r3_wellord1(sK0,X0,sK2)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(sK3(sK1,sK0,k2_funct_1(sK2)),k2_relat_1(sK2))
        | ~ v2_funct_1(sK2) )
    | ~ spl8_145 ),
    inference(subsumption_resolution,[],[f43796,f66])).

fof(f43796,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2))))),X0)
        | ~ r3_wellord1(sK0,X0,sK2)
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(sK3(sK1,sK0,k2_funct_1(sK2)),k2_relat_1(sK2))
        | ~ v2_funct_1(sK2) )
    | ~ spl8_145 ),
    inference(subsumption_resolution,[],[f43793,f67])).

fof(f43793,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2))))),X0)
        | ~ r3_wellord1(sK0,X0,sK2)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(sK3(sK1,sK0,k2_funct_1(sK2)),k2_relat_1(sK2))
        | ~ v2_funct_1(sK2) )
    | ~ spl8_145 ),
    inference(duplicate_literal_removal,[],[f43786])).

fof(f43786,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2))))),X0)
        | ~ r3_wellord1(sK0,X0,sK2)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(sK3(sK1,sK0,k2_funct_1(sK2)),k2_relat_1(sK2))
        | ~ v2_funct_1(sK2)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl8_145 ),
    inference(superposition,[],[f6253,f95])).

fof(f6253,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(k1_funct_1(X0,k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2)))),k1_funct_1(X0,k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2))))),X1)
        | ~ r3_wellord1(sK0,X1,X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1) )
    | ~ spl8_145 ),
    inference(subsumption_resolution,[],[f6252,f3981])).

fof(f3981,plain,(
    r2_hidden(k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),k1_relat_1(sK2)) ),
    inference(resolution,[],[f842,f983])).

fof(f842,plain,(
    ! [X100] :
      ( ~ r2_hidden(X100,k2_relat_1(sK2))
      | r2_hidden(k1_funct_1(k2_funct_1(sK2),X100),k1_relat_1(sK2)) ) ),
    inference(forward_demodulation,[],[f841,f713])).

fof(f841,plain,(
    ! [X100] :
      ( r2_hidden(k1_funct_1(k2_funct_1(sK2),X100),k1_relat_1(sK2))
      | ~ r2_hidden(X100,k1_relat_1(k2_funct_1(sK2))) ) ),
    inference(forward_demodulation,[],[f840,f711])).

fof(f840,plain,(
    ! [X100] :
      ( r2_hidden(k1_funct_1(k2_funct_1(sK2),X100),k2_relat_1(k2_funct_1(sK2)))
      | ~ r2_hidden(X100,k1_relat_1(k2_funct_1(sK2))) ) ),
    inference(subsumption_resolution,[],[f772,f554])).

fof(f772,plain,(
    ! [X100] :
      ( r2_hidden(k1_funct_1(k2_funct_1(sK2),X100),k2_relat_1(k2_funct_1(sK2)))
      | ~ r2_hidden(X100,k1_relat_1(k2_funct_1(sK2)))
      | ~ v1_funct_1(k2_funct_1(sK2)) ) ),
    inference(resolution,[],[f553,f102])).

fof(f102,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK5(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK5(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK6(X0,X1)) = sK5(X0,X1)
                  & r2_hidden(sK6(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK5(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK7(X0,X5)) = X5
                    & r2_hidden(sK7(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f59,f62,f61,f60])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK5(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK5(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X1)) = X2
        & r2_hidden(sK6(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK7(X0,X5)) = X5
        & r2_hidden(sK7(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/wellord1__t49_wellord1.p',d5_funct_1)).

fof(f6252,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),k1_relat_1(sK2))
        | ~ r2_hidden(k4_tarski(k1_funct_1(X0,k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2)))),k1_funct_1(X0,k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2))))),X1)
        | ~ r3_wellord1(sK0,X1,X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1) )
    | ~ spl8_145 ),
    inference(forward_demodulation,[],[f6251,f663])).

fof(f6251,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(k1_funct_1(X0,k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2)))),k1_funct_1(X0,k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2))))),X1)
        | ~ r2_hidden(k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),k3_relat_1(sK0))
        | ~ r3_wellord1(sK0,X1,X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1) )
    | ~ spl8_145 ),
    inference(subsumption_resolution,[],[f6250,f3982])).

fof(f3982,plain,(
    r2_hidden(k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2))),k1_relat_1(sK2)) ),
    inference(resolution,[],[f842,f994])).

fof(f6250,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2))),k1_relat_1(sK2))
        | ~ r2_hidden(k4_tarski(k1_funct_1(X0,k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2)))),k1_funct_1(X0,k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2))))),X1)
        | ~ r2_hidden(k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),k3_relat_1(sK0))
        | ~ r3_wellord1(sK0,X1,X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1) )
    | ~ spl8_145 ),
    inference(forward_demodulation,[],[f6249,f663])).

fof(f6249,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(k1_funct_1(X0,k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2)))),k1_funct_1(X0,k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2))))),X1)
        | ~ r2_hidden(k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2))),k3_relat_1(sK0))
        | ~ r2_hidden(k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),k3_relat_1(sK0))
        | ~ r3_wellord1(sK0,X1,X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1) )
    | ~ spl8_145 ),
    inference(subsumption_resolution,[],[f6247,f64])).

fof(f6247,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(k1_funct_1(X0,k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2)))),k1_funct_1(X0,k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2))))),X1)
        | ~ r2_hidden(k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2))),k3_relat_1(sK0))
        | ~ r2_hidden(k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),k3_relat_1(sK0))
        | ~ r3_wellord1(sK0,X1,X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(sK0) )
    | ~ spl8_145 ),
    inference(resolution,[],[f1012,f83])).

fof(f83,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X5),k1_funct_1(X2,X6)),X1)
      | ~ r2_hidden(X6,k3_relat_1(X0))
      | ~ r2_hidden(X5,k3_relat_1(X0))
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f1028,plain,
    ( ~ spl8_143
    | ~ spl8_145 ),
    inference(avatar_split_clause,[],[f1027,f1011,f1005])).

fof(f1027,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2)))),sK0)
    | ~ r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),sK4(sK1,sK0,k2_funct_1(sK2))),sK1) ),
    inference(subsumption_resolution,[],[f1026,f713])).

fof(f1026,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | ~ r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2)))),sK0)
    | ~ r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),sK4(sK1,sK0,k2_funct_1(sK2))),sK1) ),
    inference(forward_demodulation,[],[f1025,f667])).

fof(f1025,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2)))),sK0)
    | ~ r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f1024,f711])).

fof(f1024,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | ~ r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2)))),sK0)
    | ~ r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1) ),
    inference(forward_demodulation,[],[f1023,f663])).

fof(f1023,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2)))),sK0)
    | ~ r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f1022,f339])).

fof(f1022,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2)))),sK0)
    | ~ r2_hidden(sK4(sK1,sK0,k2_funct_1(sK2)),k3_relat_1(sK1))
    | ~ r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f1021,f338])).

fof(f1021,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2)))),sK0)
    | ~ r2_hidden(sK4(sK1,sK0,k2_funct_1(sK2)),k3_relat_1(sK1))
    | ~ r2_hidden(sK3(sK1,sK0,k2_funct_1(sK2)),k3_relat_1(sK1))
    | ~ r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f1020,f65])).

fof(f1020,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2)))),sK0)
    | ~ r2_hidden(sK4(sK1,sK0,k2_funct_1(sK2)),k3_relat_1(sK1))
    | ~ r2_hidden(sK3(sK1,sK0,k2_funct_1(sK2)),k3_relat_1(sK1))
    | ~ r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f1019,f64])).

fof(f1019,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2)))),sK0)
    | ~ r2_hidden(sK4(sK1,sK0,k2_funct_1(sK2)),k3_relat_1(sK1))
    | ~ r2_hidden(sK3(sK1,sK0,k2_funct_1(sK2)),k3_relat_1(sK1))
    | ~ r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f1018,f553])).

fof(f1018,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2)))),sK0)
    | ~ r2_hidden(sK4(sK1,sK0,k2_funct_1(sK2)),k3_relat_1(sK1))
    | ~ r2_hidden(sK3(sK1,sK0,k2_funct_1(sK2)),k3_relat_1(sK1))
    | ~ r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f1017,f554])).

fof(f1017,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2)))),sK0)
    | ~ r2_hidden(sK4(sK1,sK0,k2_funct_1(sK2)),k3_relat_1(sK1))
    | ~ r2_hidden(sK3(sK1,sK0,k2_funct_1(sK2)),k3_relat_1(sK1))
    | ~ r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f972,f709])).

fof(f972,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2)))),sK0)
    | ~ r2_hidden(sK4(sK1,sK0,k2_funct_1(sK2)),k3_relat_1(sK1))
    | ~ r2_hidden(sK3(sK1,sK0,k2_funct_1(sK2)),k3_relat_1(sK1))
    | ~ r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK1)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f69,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r3_wellord1(X0,X1,X2)
      | ~ r2_hidden(k4_tarski(k1_funct_1(X2,sK3(X0,X1,X2)),k1_funct_1(X2,sK4(X0,X1,X2))),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),k3_relat_1(X0))
      | ~ r2_hidden(sK3(X0,X1,X2),k3_relat_1(X0))
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
      | ~ v2_funct_1(X2)
      | k2_relat_1(X2) != k3_relat_1(X1)
      | k1_relat_1(X2) != k3_relat_1(X0)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).
%------------------------------------------------------------------------------
