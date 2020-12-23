%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 257 expanded)
%              Number of leaves         :   28 (  91 expanded)
%              Depth                    :   17
%              Number of atoms          :  515 (1339 expanded)
%              Number of equality atoms :  201 ( 489 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1156,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f106,f463,f822,f1000,f1001,f1053,f1155])).

fof(f1155,plain,(
    ~ spl13_50 ),
    inference(avatar_contradiction_clause,[],[f1135])).

fof(f1135,plain,
    ( $false
    | ~ spl13_50 ),
    inference(unit_resulting_resolution,[],[f87,f1052,f428])).

fof(f428,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k2_relat_1(sK5(X1,X2)),X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f191,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f191,plain,(
    ! [X6,X4,X5] :
      ( r2_hidden(X5,k2_relat_1(sK5(X4,X5)))
      | ~ r2_hidden(X6,X4) ) ),
    inference(duplicate_literal_removal,[],[f190])).

fof(f190,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X6,X4)
      | r2_hidden(X5,k2_relat_1(sK5(X4,X5)))
      | ~ r2_hidden(X6,X4) ) ),
    inference(forward_demodulation,[],[f189,f68])).

fof(f68,plain,(
    ! [X0,X1] : k1_relat_1(sK5(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK5(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK5(X0,X1)) = X0
      & v1_funct_1(sK5(X0,X1))
      & v1_relat_1(sK5(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f19,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK5(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK5(X0,X1)) = X0
        & v1_funct_1(sK5(X0,X1))
        & v1_relat_1(sK5(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f189,plain,(
    ! [X6,X4,X5] :
      ( r2_hidden(X5,k2_relat_1(sK5(X4,X5)))
      | ~ r2_hidden(X6,k1_relat_1(sK5(X4,X5)))
      | ~ r2_hidden(X6,X4) ) ),
    inference(subsumption_resolution,[],[f188,f66])).

fof(f66,plain,(
    ! [X0,X1] : v1_relat_1(sK5(X0,X1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f188,plain,(
    ! [X6,X4,X5] :
      ( r2_hidden(X5,k2_relat_1(sK5(X4,X5)))
      | ~ r2_hidden(X6,k1_relat_1(sK5(X4,X5)))
      | ~ v1_relat_1(sK5(X4,X5))
      | ~ r2_hidden(X6,X4) ) ),
    inference(subsumption_resolution,[],[f178,f67])).

fof(f67,plain,(
    ! [X0,X1] : v1_funct_1(sK5(X0,X1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f178,plain,(
    ! [X6,X4,X5] :
      ( r2_hidden(X5,k2_relat_1(sK5(X4,X5)))
      | ~ r2_hidden(X6,k1_relat_1(sK5(X4,X5)))
      | ~ v1_funct_1(sK5(X4,X5))
      | ~ v1_relat_1(sK5(X4,X5))
      | ~ r2_hidden(X6,X4) ) ),
    inference(superposition,[],[f94,f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK5(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f94,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK9(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK9(X0,X1),X1) )
              & ( ( sK9(X0,X1) = k1_funct_1(X0,sK10(X0,X1))
                  & r2_hidden(sK10(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK9(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK11(X0,X5)) = X5
                    & r2_hidden(sK11(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f44,f47,f46,f45])).

% (26741)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
fof(f45,plain,(
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
              ( k1_funct_1(X0,X3) != sK9(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK9(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK9(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK9(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK9(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK9(X0,X1) = k1_funct_1(X0,sK10(X0,X1))
        & r2_hidden(sK10(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK11(X0,X5)) = X5
        & r2_hidden(sK11(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

% (26733)Refutation not found, incomplete strategy% (26733)------------------------------
% (26733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26733)Termination reason: Refutation not found, incomplete strategy

% (26733)Memory used [KB]: 1791
% (26733)Time elapsed: 0.149 s
% (26733)------------------------------
% (26733)------------------------------
fof(f20,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f1052,plain,
    ( ! [X0] : r2_hidden(X0,k2_relat_1(sK1(sK0)))
    | ~ spl13_50 ),
    inference(avatar_component_clause,[],[f1051])).

fof(f1051,plain,
    ( spl13_50
  <=> ! [X0] : r2_hidden(X0,k2_relat_1(sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_50])])).

fof(f87,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f1053,plain,
    ( spl13_5
    | spl13_50 ),
    inference(avatar_split_clause,[],[f430,f1051,f154])).

fof(f154,plain,
    ( spl13_5
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).

fof(f430,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_relat_1(sK1(sK0)))
      | ~ r2_hidden(X1,sK0) ) ),
    inference(superposition,[],[f191,f171])).

fof(f171,plain,(
    ! [X0] : sK1(sK0) = sK5(sK0,X0) ),
    inference(equality_resolution,[],[f167])).

fof(f167,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | sK5(X0,X1) = sK1(sK0) ) ),
    inference(equality_resolution,[],[f131])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( sK0 != X2
      | sK5(X0,X1) = sK1(X2)
      | sK0 != X0 ) ),
    inference(subsumption_resolution,[],[f130,f66])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( sK0 != X0
      | sK5(X0,X1) = sK1(X2)
      | sK0 != X2
      | ~ v1_relat_1(sK5(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f128,f67])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( sK0 != X0
      | sK5(X0,X1) = sK1(X2)
      | sK0 != X2
      | ~ v1_funct_1(sK5(X0,X1))
      | ~ v1_relat_1(sK5(X0,X1)) ) ),
    inference(superposition,[],[f115,f68])).

fof(f115,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != sK0
      | sK1(X0) = X1
      | sK0 != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f114,f53])).

fof(f53,plain,(
    ! [X0] : v1_relat_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK1(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK1(X0)) = X0
      & v1_funct_1(sK1(X0))
      & v1_relat_1(sK1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK1(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK1(X0)) = X0
        & v1_funct_1(sK1(X0))
        & v1_relat_1(sK1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f114,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | sK1(X0) = X1
      | k1_relat_1(X1) != sK0
      | ~ v1_relat_1(sK1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f113,f54])).

fof(f54,plain,(
    ! [X0] : v1_funct_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f113,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | sK1(X0) = X1
      | k1_relat_1(X1) != sK0
      | ~ v1_funct_1(sK1(X0))
      | ~ v1_relat_1(sK1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f51,f55])).

fof(f55,plain,(
    ! [X0] : k1_relat_1(sK1(X0)) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f51,plain,(
    ! [X2,X1] :
      ( k1_relat_1(X2) != sK0
      | X1 = X2
      | k1_relat_1(X1) != sK0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( k1_xboole_0 != sK0
    & ! [X1] :
        ( ! [X2] :
            ( X1 = X2
            | k1_relat_1(X2) != sK0
            | k1_relat_1(X1) != sK0
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k1_relat_1(X2) != X0
                | k1_relat_1(X1) != X0
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
   => ( k1_xboole_0 != sK0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != sK0
              | k1_relat_1(X1) != sK0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( k1_relat_1(X2) = X0
                    & k1_relat_1(X1) = X0 )
                 => X1 = X2 ) ) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( k1_relat_1(X2) = X0
                  & k1_relat_1(X1) = X0 )
               => X1 = X2 ) ) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).

fof(f1001,plain,
    ( k1_xboole_0 != sK1(sK0)
    | k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | sK0 != k2_relat_1(sK1(sK0))
    | k1_xboole_0 = sK0 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1000,plain,
    ( spl13_44
    | ~ spl13_5 ),
    inference(avatar_split_clause,[],[f995,f154,f997])).

fof(f997,plain,
    ( spl13_44
  <=> k1_xboole_0 = sK1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_44])])).

fof(f995,plain,
    ( k1_xboole_0 = sK1(sK0)
    | ~ spl13_5 ),
    inference(resolution,[],[f474,f155])).

fof(f155,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl13_5 ),
    inference(avatar_component_clause,[],[f154])).

fof(f474,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK1(X0)),X0)
      | k1_xboole_0 = sK1(X0) ) ),
    inference(subsumption_resolution,[],[f471,f53])).

fof(f471,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK1(X0)),X0)
      | ~ v1_relat_1(sK1(X0))
      | k1_xboole_0 = sK1(X0) ) ),
    inference(superposition,[],[f172,f55])).

fof(f172,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f57,f91])).

fof(f91,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

% (26741)Refutation not found, incomplete strategy% (26741)------------------------------
% (26741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26741)Termination reason: Refutation not found, incomplete strategy

% (26741)Memory used [KB]: 6268
% (26741)Time elapsed: 0.152 s
% (26741)------------------------------
% (26741)------------------------------
fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f38,f41,f40,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f18,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
     => r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

% (26742)Refutation not found, incomplete strategy% (26742)------------------------------
% (26742)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26742)Termination reason: Refutation not found, incomplete strategy

% (26742)Memory used [KB]: 6268
% (26742)Time elapsed: 0.130 s
% (26742)------------------------------
% (26742)------------------------------
fof(f822,plain,
    ( spl13_41
    | ~ spl13_5
    | ~ spl13_28 ),
    inference(avatar_split_clause,[],[f801,f460,f154,f819])).

fof(f819,plain,
    ( spl13_41
  <=> sK0 = k2_relat_1(sK1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_41])])).

fof(f460,plain,
    ( spl13_28
  <=> sK0 = k1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_28])])).

fof(f801,plain,
    ( sK0 = k2_relat_1(sK1(sK0))
    | ~ spl13_5
    | ~ spl13_28 ),
    inference(resolution,[],[f478,f521])).

fof(f521,plain,
    ( ! [X5] : ~ r2_hidden(X5,k2_relat_1(sK1(sK0)))
    | ~ spl13_5 ),
    inference(resolution,[],[f220,f155])).

fof(f220,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK11(sK1(X1),X2),X1)
      | ~ r2_hidden(X2,k2_relat_1(sK1(X1))) ) ),
    inference(subsumption_resolution,[],[f219,f53])).

fof(f219,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK11(sK1(X1),X2),X1)
      | ~ r2_hidden(X2,k2_relat_1(sK1(X1)))
      | ~ v1_relat_1(sK1(X1)) ) ),
    inference(subsumption_resolution,[],[f211,f54])).

fof(f211,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK11(sK1(X1),X2),X1)
      | ~ r2_hidden(X2,k2_relat_1(sK1(X1)))
      | ~ v1_funct_1(sK1(X1))
      | ~ v1_relat_1(sK1(X1)) ) ),
    inference(superposition,[],[f96,f55])).

fof(f96,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK11(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK11(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f478,plain,
    ( ! [X9] :
        ( r2_hidden(sK6(sK0,X9),X9)
        | sK0 = X9 )
    | ~ spl13_5
    | ~ spl13_28 ),
    inference(backward_demodulation,[],[f265,f462])).

fof(f462,plain,
    ( sK0 = k1_relat_1(sK0)
    | ~ spl13_28 ),
    inference(avatar_component_clause,[],[f460])).

fof(f265,plain,
    ( ! [X9] :
        ( r2_hidden(sK6(sK0,X9),X9)
        | k1_relat_1(sK0) = X9 )
    | ~ spl13_5 ),
    inference(resolution,[],[f72,f155])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
      | k1_relat_1(X0) = X1
      | r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f463,plain,
    ( spl13_28
    | ~ spl13_5 ),
    inference(avatar_split_clause,[],[f438,f154,f460])).

fof(f438,plain,
    ( sK0 = k1_relat_1(sK0)
    | ~ spl13_5 ),
    inference(resolution,[],[f265,f155])).

fof(f106,plain,(
    spl13_2 ),
    inference(avatar_split_clause,[],[f59,f103])).

fof(f103,plain,
    ( spl13_2
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f59,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f101,plain,(
    ~ spl13_1 ),
    inference(avatar_split_clause,[],[f52,f98])).

fof(f98,plain,
    ( spl13_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f52,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:28:10 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (26737)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.50  % (26745)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (26745)Refutation not found, incomplete strategy% (26745)------------------------------
% 0.21/0.50  % (26745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (26729)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % (26745)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (26745)Memory used [KB]: 1663
% 0.21/0.51  % (26745)Time elapsed: 0.084 s
% 0.21/0.51  % (26745)------------------------------
% 0.21/0.51  % (26745)------------------------------
% 0.21/0.51  % (26721)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (26738)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (26731)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (26718)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (26717)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (26732)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  % (26717)Refutation not found, incomplete strategy% (26717)------------------------------
% 0.21/0.53  % (26717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (26717)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (26717)Memory used [KB]: 1663
% 0.21/0.53  % (26717)Time elapsed: 0.114 s
% 0.21/0.53  % (26717)------------------------------
% 0.21/0.53  % (26717)------------------------------
% 0.21/0.54  % (26720)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (26730)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (26733)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (26723)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (26722)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (26716)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (26719)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (26735)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (26744)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (26742)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (26743)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (26736)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (26724)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.55  % (26743)Refutation not found, incomplete strategy% (26743)------------------------------
% 0.21/0.55  % (26743)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (26743)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (26743)Memory used [KB]: 6268
% 0.21/0.55  % (26743)Time elapsed: 0.130 s
% 0.21/0.55  % (26743)------------------------------
% 0.21/0.55  % (26743)------------------------------
% 0.21/0.55  % (26725)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (26734)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (26727)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (26734)Refutation not found, incomplete strategy% (26734)------------------------------
% 0.21/0.55  % (26734)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (26734)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (26734)Memory used [KB]: 1791
% 0.21/0.55  % (26734)Time elapsed: 0.138 s
% 0.21/0.55  % (26734)------------------------------
% 0.21/0.55  % (26734)------------------------------
% 0.21/0.55  % (26727)Refutation not found, incomplete strategy% (26727)------------------------------
% 0.21/0.55  % (26727)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (26727)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (26727)Memory used [KB]: 6268
% 0.21/0.55  % (26727)Time elapsed: 0.145 s
% 0.21/0.55  % (26727)------------------------------
% 0.21/0.55  % (26727)------------------------------
% 0.21/0.55  % (26726)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (26728)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.56  % (26732)Refutation not found, incomplete strategy% (26732)------------------------------
% 0.21/0.56  % (26732)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (26732)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (26732)Memory used [KB]: 10746
% 0.21/0.56  % (26732)Time elapsed: 0.136 s
% 0.21/0.56  % (26732)------------------------------
% 0.21/0.56  % (26732)------------------------------
% 0.21/0.56  % (26739)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.56  % (26728)Refutation not found, incomplete strategy% (26728)------------------------------
% 0.21/0.56  % (26728)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (26728)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (26728)Memory used [KB]: 10618
% 0.21/0.56  % (26728)Time elapsed: 0.140 s
% 0.21/0.56  % (26728)------------------------------
% 0.21/0.56  % (26728)------------------------------
% 0.21/0.56  % (26740)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.56  % (26740)Refutation not found, incomplete strategy% (26740)------------------------------
% 0.21/0.56  % (26740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (26740)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (26740)Memory used [KB]: 10746
% 0.21/0.56  % (26740)Time elapsed: 0.140 s
% 0.21/0.56  % (26740)------------------------------
% 0.21/0.56  % (26740)------------------------------
% 0.21/0.56  % (26737)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f1156,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f101,f106,f463,f822,f1000,f1001,f1053,f1155])).
% 0.21/0.56  fof(f1155,plain,(
% 0.21/0.56    ~spl13_50),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f1135])).
% 0.21/0.56  fof(f1135,plain,(
% 0.21/0.56    $false | ~spl13_50),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f87,f1052,f428])).
% 0.21/0.56  fof(f428,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r2_hidden(k2_relat_1(sK5(X1,X2)),X2) | ~r2_hidden(X0,X1)) )),
% 0.21/0.56    inference(resolution,[],[f191,f84])).
% 0.21/0.56  fof(f84,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f23])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.21/0.56  fof(f191,plain,(
% 0.21/0.56    ( ! [X6,X4,X5] : (r2_hidden(X5,k2_relat_1(sK5(X4,X5))) | ~r2_hidden(X6,X4)) )),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f190])).
% 0.21/0.56  fof(f190,plain,(
% 0.21/0.56    ( ! [X6,X4,X5] : (~r2_hidden(X6,X4) | r2_hidden(X5,k2_relat_1(sK5(X4,X5))) | ~r2_hidden(X6,X4)) )),
% 0.21/0.56    inference(forward_demodulation,[],[f189,f68])).
% 0.21/0.56  fof(f68,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k1_relat_1(sK5(X0,X1)) = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f36])).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    ! [X0,X1] : (! [X3] : (k1_funct_1(sK5(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK5(X0,X1)) = X0 & v1_funct_1(sK5(X0,X1)) & v1_relat_1(sK5(X0,X1)))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f19,f35])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK5(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK5(X0,X1)) = X0 & v1_funct_1(sK5(X0,X1)) & v1_relat_1(sK5(X0,X1))))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.56    inference(ennf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,axiom,(
% 0.21/0.56    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 0.21/0.56  fof(f189,plain,(
% 0.21/0.56    ( ! [X6,X4,X5] : (r2_hidden(X5,k2_relat_1(sK5(X4,X5))) | ~r2_hidden(X6,k1_relat_1(sK5(X4,X5))) | ~r2_hidden(X6,X4)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f188,f66])).
% 0.21/0.56  fof(f66,plain,(
% 0.21/0.56    ( ! [X0,X1] : (v1_relat_1(sK5(X0,X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f36])).
% 0.21/0.56  fof(f188,plain,(
% 0.21/0.56    ( ! [X6,X4,X5] : (r2_hidden(X5,k2_relat_1(sK5(X4,X5))) | ~r2_hidden(X6,k1_relat_1(sK5(X4,X5))) | ~v1_relat_1(sK5(X4,X5)) | ~r2_hidden(X6,X4)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f178,f67])).
% 0.21/0.56  fof(f67,plain,(
% 0.21/0.56    ( ! [X0,X1] : (v1_funct_1(sK5(X0,X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f36])).
% 0.21/0.56  fof(f178,plain,(
% 0.21/0.56    ( ! [X6,X4,X5] : (r2_hidden(X5,k2_relat_1(sK5(X4,X5))) | ~r2_hidden(X6,k1_relat_1(sK5(X4,X5))) | ~v1_funct_1(sK5(X4,X5)) | ~v1_relat_1(sK5(X4,X5)) | ~r2_hidden(X6,X4)) )),
% 0.21/0.56    inference(superposition,[],[f94,f69])).
% 0.21/0.56  fof(f69,plain,(
% 0.21/0.56    ( ! [X0,X3,X1] : (k1_funct_1(sK5(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f36])).
% 0.21/0.56  fof(f94,plain,(
% 0.21/0.56    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(equality_resolution,[],[f93])).
% 0.21/0.56  fof(f93,plain,(
% 0.21/0.56    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(equality_resolution,[],[f76])).
% 0.21/0.56  fof(f76,plain,(
% 0.21/0.56    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f48])).
% 0.21/0.56  fof(f48,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK9(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK9(X0,X1),X1)) & ((sK9(X0,X1) = k1_funct_1(X0,sK10(X0,X1)) & r2_hidden(sK10(X0,X1),k1_relat_1(X0))) | r2_hidden(sK9(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK11(X0,X5)) = X5 & r2_hidden(sK11(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f44,f47,f46,f45])).
% 0.21/0.56  % (26741)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.56  fof(f45,plain,(
% 0.21/0.56    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK9(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK9(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK9(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK9(X0,X1),X1))))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK9(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK9(X0,X1) = k1_funct_1(X0,sK10(X0,X1)) & r2_hidden(sK10(X0,X1),k1_relat_1(X0))))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f47,plain,(
% 0.21/0.56    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK11(X0,X5)) = X5 & r2_hidden(sK11(X0,X5),k1_relat_1(X0))))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f44,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(rectify,[],[f43])).
% 0.21/0.56  fof(f43,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(nnf_transformation,[],[f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(flattening,[],[f20])).
% 0.21/0.56  % (26733)Refutation not found, incomplete strategy% (26733)------------------------------
% 0.21/0.56  % (26733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (26733)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (26733)Memory used [KB]: 1791
% 0.21/0.56  % (26733)Time elapsed: 0.149 s
% 0.21/0.56  % (26733)------------------------------
% 0.21/0.56  % (26733)------------------------------
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 0.21/0.56  fof(f1052,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK1(sK0)))) ) | ~spl13_50),
% 0.21/0.56    inference(avatar_component_clause,[],[f1051])).
% 0.21/0.56  fof(f1051,plain,(
% 0.21/0.56    spl13_50 <=> ! [X0] : r2_hidden(X0,k2_relat_1(sK1(sK0)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_50])])).
% 0.21/0.56  fof(f87,plain,(
% 0.21/0.56    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 0.21/0.56    inference(equality_resolution,[],[f86])).
% 0.21/0.56  fof(f86,plain,(
% 0.21/0.56    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 0.21/0.56    inference(equality_resolution,[],[f62])).
% 0.21/0.56  fof(f62,plain,(
% 0.21/0.56    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.21/0.56    inference(cnf_transformation,[],[f34])).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.56    inference(rectify,[],[f31])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.56    inference(flattening,[],[f30])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.56    inference(nnf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.21/0.56  fof(f1053,plain,(
% 0.21/0.56    spl13_5 | spl13_50),
% 0.21/0.56    inference(avatar_split_clause,[],[f430,f1051,f154])).
% 0.21/0.56  fof(f154,plain,(
% 0.21/0.56    spl13_5 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).
% 0.21/0.56  fof(f430,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r2_hidden(X0,k2_relat_1(sK1(sK0))) | ~r2_hidden(X1,sK0)) )),
% 0.21/0.56    inference(superposition,[],[f191,f171])).
% 0.21/0.56  fof(f171,plain,(
% 0.21/0.56    ( ! [X0] : (sK1(sK0) = sK5(sK0,X0)) )),
% 0.21/0.56    inference(equality_resolution,[],[f167])).
% 0.21/0.56  fof(f167,plain,(
% 0.21/0.56    ( ! [X0,X1] : (sK0 != X0 | sK5(X0,X1) = sK1(sK0)) )),
% 0.21/0.56    inference(equality_resolution,[],[f131])).
% 0.21/0.56  fof(f131,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (sK0 != X2 | sK5(X0,X1) = sK1(X2) | sK0 != X0) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f130,f66])).
% 0.21/0.56  fof(f130,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (sK0 != X0 | sK5(X0,X1) = sK1(X2) | sK0 != X2 | ~v1_relat_1(sK5(X0,X1))) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f128,f67])).
% 0.21/0.56  fof(f128,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (sK0 != X0 | sK5(X0,X1) = sK1(X2) | sK0 != X2 | ~v1_funct_1(sK5(X0,X1)) | ~v1_relat_1(sK5(X0,X1))) )),
% 0.21/0.56    inference(superposition,[],[f115,f68])).
% 0.21/0.56  fof(f115,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k1_relat_1(X1) != sK0 | sK1(X0) = X1 | sK0 != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f114,f53])).
% 0.21/0.56  fof(f53,plain,(
% 0.21/0.56    ( ! [X0] : (v1_relat_1(sK1(X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ! [X0] : (! [X2] : (k1_xboole_0 = k1_funct_1(sK1(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK1(X0)) = X0 & v1_funct_1(sK1(X0)) & v1_relat_1(sK1(X0)))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ! [X0] : (? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_xboole_0 = k1_funct_1(sK1(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK1(X0)) = X0 & v1_funct_1(sK1(X0)) & v1_relat_1(sK1(X0))))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f16,plain,(
% 0.21/0.56    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,axiom,(
% 0.21/0.56    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 0.21/0.56  fof(f114,plain,(
% 0.21/0.56    ( ! [X0,X1] : (sK0 != X0 | sK1(X0) = X1 | k1_relat_1(X1) != sK0 | ~v1_relat_1(sK1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f113,f54])).
% 0.21/0.56  fof(f54,plain,(
% 0.21/0.56    ( ! [X0] : (v1_funct_1(sK1(X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f27])).
% 0.21/0.56  fof(f113,plain,(
% 0.21/0.56    ( ! [X0,X1] : (sK0 != X0 | sK1(X0) = X1 | k1_relat_1(X1) != sK0 | ~v1_funct_1(sK1(X0)) | ~v1_relat_1(sK1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.56    inference(superposition,[],[f51,f55])).
% 0.21/0.56  fof(f55,plain,(
% 0.21/0.56    ( ! [X0] : (k1_relat_1(sK1(X0)) = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f27])).
% 0.21/0.56  fof(f51,plain,(
% 0.21/0.56    ( ! [X2,X1] : (k1_relat_1(X2) != sK0 | X1 = X2 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    k1_xboole_0 != sK0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) => (k1_xboole_0 != sK0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f15,plain,(
% 0.21/0.56    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.56    inference(flattening,[],[f14])).
% 0.21/0.56  fof(f14,plain,(
% 0.21/0.56    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 0.21/0.56    inference(ennf_transformation,[],[f13])).
% 0.21/0.56  fof(f13,negated_conjecture,(
% 0.21/0.56    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.21/0.56    inference(negated_conjecture,[],[f12])).
% 0.21/0.56  fof(f12,conjecture,(
% 0.21/0.56    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).
% 0.21/0.56  fof(f1001,plain,(
% 0.21/0.56    k1_xboole_0 != sK1(sK0) | k1_xboole_0 != k2_relat_1(k1_xboole_0) | sK0 != k2_relat_1(sK1(sK0)) | k1_xboole_0 = sK0),
% 0.21/0.56    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.56  fof(f1000,plain,(
% 0.21/0.56    spl13_44 | ~spl13_5),
% 0.21/0.56    inference(avatar_split_clause,[],[f995,f154,f997])).
% 0.21/0.56  fof(f997,plain,(
% 0.21/0.56    spl13_44 <=> k1_xboole_0 = sK1(sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_44])])).
% 0.21/0.56  fof(f995,plain,(
% 0.21/0.56    k1_xboole_0 = sK1(sK0) | ~spl13_5),
% 0.21/0.56    inference(resolution,[],[f474,f155])).
% 0.21/0.56  fof(f155,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl13_5),
% 0.21/0.56    inference(avatar_component_clause,[],[f154])).
% 0.21/0.56  fof(f474,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK2(sK1(X0)),X0) | k1_xboole_0 = sK1(X0)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f471,f53])).
% 0.21/0.56  fof(f471,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK2(sK1(X0)),X0) | ~v1_relat_1(sK1(X0)) | k1_xboole_0 = sK1(X0)) )),
% 0.21/0.56    inference(superposition,[],[f172,f55])).
% 0.21/0.56  fof(f172,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK2(X0),k1_relat_1(X0)) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(resolution,[],[f57,f91])).
% 0.21/0.56  fof(f91,plain,(
% 0.21/0.56    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X5,X6),X0) | r2_hidden(X5,k1_relat_1(X0))) )),
% 0.21/0.56    inference(equality_resolution,[],[f71])).
% 0.21/0.56  fof(f71,plain,(
% 0.21/0.56    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f42])).
% 0.21/0.56  % (26741)Refutation not found, incomplete strategy% (26741)------------------------------
% 0.21/0.56  % (26741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (26741)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (26741)Memory used [KB]: 6268
% 0.21/0.56  % (26741)Time elapsed: 0.152 s
% 0.21/0.56  % (26741)------------------------------
% 0.21/0.56  % (26741)------------------------------
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f38,f41,f40,f39])).
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f38,plain,(
% 0.21/0.56    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.56    inference(rectify,[],[f37])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.56    inference(nnf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.21/0.56  fof(f57,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f29])).
% 0.21/0.56  fof(f29,plain,(
% 0.21/0.56    ! [X0] : (k1_xboole_0 = X0 | r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f18,f28])).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    ! [X0] : (? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) => r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    ! [X0] : (k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(flattening,[],[f17])).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    ! [X0] : ((k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => (! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) => k1_xboole_0 = X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).
% 0.21/0.57  % (26742)Refutation not found, incomplete strategy% (26742)------------------------------
% 0.21/0.57  % (26742)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (26742)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (26742)Memory used [KB]: 6268
% 0.21/0.57  % (26742)Time elapsed: 0.130 s
% 0.21/0.57  % (26742)------------------------------
% 0.21/0.57  % (26742)------------------------------
% 0.21/0.57  fof(f822,plain,(
% 0.21/0.57    spl13_41 | ~spl13_5 | ~spl13_28),
% 0.21/0.57    inference(avatar_split_clause,[],[f801,f460,f154,f819])).
% 0.21/0.57  fof(f819,plain,(
% 0.21/0.57    spl13_41 <=> sK0 = k2_relat_1(sK1(sK0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_41])])).
% 0.21/0.57  fof(f460,plain,(
% 0.21/0.57    spl13_28 <=> sK0 = k1_relat_1(sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_28])])).
% 0.21/0.57  fof(f801,plain,(
% 0.21/0.57    sK0 = k2_relat_1(sK1(sK0)) | (~spl13_5 | ~spl13_28)),
% 0.21/0.57    inference(resolution,[],[f478,f521])).
% 0.21/0.57  fof(f521,plain,(
% 0.21/0.57    ( ! [X5] : (~r2_hidden(X5,k2_relat_1(sK1(sK0)))) ) | ~spl13_5),
% 0.21/0.57    inference(resolution,[],[f220,f155])).
% 0.21/0.57  fof(f220,plain,(
% 0.21/0.57    ( ! [X2,X1] : (r2_hidden(sK11(sK1(X1),X2),X1) | ~r2_hidden(X2,k2_relat_1(sK1(X1)))) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f219,f53])).
% 0.21/0.57  fof(f219,plain,(
% 0.21/0.57    ( ! [X2,X1] : (r2_hidden(sK11(sK1(X1),X2),X1) | ~r2_hidden(X2,k2_relat_1(sK1(X1))) | ~v1_relat_1(sK1(X1))) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f211,f54])).
% 0.21/0.57  fof(f211,plain,(
% 0.21/0.57    ( ! [X2,X1] : (r2_hidden(sK11(sK1(X1),X2),X1) | ~r2_hidden(X2,k2_relat_1(sK1(X1))) | ~v1_funct_1(sK1(X1)) | ~v1_relat_1(sK1(X1))) )),
% 0.21/0.57    inference(superposition,[],[f96,f55])).
% 0.21/0.57  fof(f96,plain,(
% 0.21/0.57    ( ! [X0,X5] : (r2_hidden(sK11(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(equality_resolution,[],[f74])).
% 0.21/0.57  fof(f74,plain,(
% 0.21/0.57    ( ! [X0,X5,X1] : (r2_hidden(sK11(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f48])).
% 0.21/0.57  fof(f478,plain,(
% 0.21/0.57    ( ! [X9] : (r2_hidden(sK6(sK0,X9),X9) | sK0 = X9) ) | (~spl13_5 | ~spl13_28)),
% 0.21/0.57    inference(backward_demodulation,[],[f265,f462])).
% 0.21/0.57  fof(f462,plain,(
% 0.21/0.57    sK0 = k1_relat_1(sK0) | ~spl13_28),
% 0.21/0.57    inference(avatar_component_clause,[],[f460])).
% 0.21/0.57  fof(f265,plain,(
% 0.21/0.57    ( ! [X9] : (r2_hidden(sK6(sK0,X9),X9) | k1_relat_1(sK0) = X9) ) | ~spl13_5),
% 0.21/0.57    inference(resolution,[],[f72,f155])).
% 0.21/0.57  fof(f72,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) | k1_relat_1(X0) = X1 | r2_hidden(sK6(X0,X1),X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f42])).
% 0.21/0.57  fof(f463,plain,(
% 0.21/0.57    spl13_28 | ~spl13_5),
% 0.21/0.57    inference(avatar_split_clause,[],[f438,f154,f460])).
% 0.21/0.57  fof(f438,plain,(
% 0.21/0.57    sK0 = k1_relat_1(sK0) | ~spl13_5),
% 0.21/0.57    inference(resolution,[],[f265,f155])).
% 0.21/0.57  fof(f106,plain,(
% 0.21/0.57    spl13_2),
% 0.21/0.57    inference(avatar_split_clause,[],[f59,f103])).
% 0.21/0.57  fof(f103,plain,(
% 0.21/0.57    spl13_2 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).
% 0.21/0.57  fof(f59,plain,(
% 0.21/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.57    inference(cnf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.57  fof(f101,plain,(
% 0.21/0.57    ~spl13_1),
% 0.21/0.57    inference(avatar_split_clause,[],[f52,f98])).
% 0.21/0.57  fof(f98,plain,(
% 0.21/0.57    spl13_1 <=> k1_xboole_0 = sK0),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    k1_xboole_0 != sK0),
% 0.21/0.57    inference(cnf_transformation,[],[f25])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (26737)------------------------------
% 0.21/0.57  % (26737)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (26737)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (26737)Memory used [KB]: 7164
% 0.21/0.57  % (26737)Time elapsed: 0.147 s
% 0.21/0.57  % (26737)------------------------------
% 0.21/0.57  % (26737)------------------------------
% 0.21/0.57  % (26715)Success in time 0.197 s
%------------------------------------------------------------------------------
