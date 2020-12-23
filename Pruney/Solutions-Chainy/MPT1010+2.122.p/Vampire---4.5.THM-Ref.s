%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 129 expanded)
%              Number of leaves         :   19 (  43 expanded)
%              Depth                    :   12
%              Number of atoms          :  324 ( 503 expanded)
%              Number of equality atoms :  178 ( 230 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f134,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f82,f87,f92,f97,f109,f120,f133])).

fof(f133,plain,
    ( ~ spl5_2
    | spl5_3
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | ~ spl5_2
    | spl5_3
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f81,f86,f127])).

fof(f127,plain,
    ( ! [X0] :
        ( sK1 = k1_funct_1(sK3,X0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl5_6 ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | sK1 = k1_funct_1(sK3,X0)
        | sK1 = k1_funct_1(sK3,X0)
        | sK1 = k1_funct_1(sK3,X0)
        | sK1 = k1_funct_1(sK3,X0)
        | sK1 = k1_funct_1(sK3,X0) )
    | ~ spl5_6 ),
    inference(resolution,[],[f104,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X7,X3,X1] :
      ( ~ r2_hidden(X7,k3_enumset1(X0,X1,X2,X3,X4))
      | X3 = X7
      | X2 = X7
      | X1 = X7
      | X0 = X7
      | X4 = X7 ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( X4 = X7
      | X3 = X7
      | X2 = X7
      | X1 = X7
      | X0 = X7
      | ~ r2_hidden(X7,X5)
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ( ( ( sK4(X0,X1,X2,X3,X4,X5) != X4
              & sK4(X0,X1,X2,X3,X4,X5) != X3
              & sK4(X0,X1,X2,X3,X4,X5) != X2
              & sK4(X0,X1,X2,X3,X4,X5) != X1
              & sK4(X0,X1,X2,X3,X4,X5) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3,X4,X5),X5) )
          & ( sK4(X0,X1,X2,X3,X4,X5) = X4
            | sK4(X0,X1,X2,X3,X4,X5) = X3
            | sK4(X0,X1,X2,X3,X4,X5) = X2
            | sK4(X0,X1,X2,X3,X4,X5) = X1
            | sK4(X0,X1,X2,X3,X4,X5) = X0
            | r2_hidden(sK4(X0,X1,X2,X3,X4,X5),X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ( X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X5) ) )
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f23])).

fof(f23,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ( ( X4 != X6
              & X3 != X6
              & X2 != X6
              & X1 != X6
              & X0 != X6 )
            | ~ r2_hidden(X6,X5) )
          & ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6
            | r2_hidden(X6,X5) ) )
     => ( ( ( sK4(X0,X1,X2,X3,X4,X5) != X4
            & sK4(X0,X1,X2,X3,X4,X5) != X3
            & sK4(X0,X1,X2,X3,X4,X5) != X2
            & sK4(X0,X1,X2,X3,X4,X5) != X1
            & sK4(X0,X1,X2,X3,X4,X5) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3,X4,X5),X5) )
        & ( sK4(X0,X1,X2,X3,X4,X5) = X4
          | sK4(X0,X1,X2,X3,X4,X5) = X3
          | sK4(X0,X1,X2,X3,X4,X5) = X2
          | sK4(X0,X1,X2,X3,X4,X5) = X1
          | sK4(X0,X1,X2,X3,X4,X5) = X0
          | r2_hidden(sK4(X0,X1,X2,X3,X4,X5),X5) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ( X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X5) ) )
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X5) ) )
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X5) ) )
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X4 != X6
              & X3 != X6
              & X2 != X6
              & X1 != X6
              & X0 != X6 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).

fof(f104,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
        | ~ r2_hidden(X0,sK0) )
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl5_6
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK3,X0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f86,plain,
    ( sK1 != k1_funct_1(sK3,sK2)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl5_3
  <=> sK1 = k1_funct_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f81,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl5_2
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f120,plain,(
    ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f71,f108,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ) ),
    inference(superposition,[],[f59,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

% (16525)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
fof(f59,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
    inference(definition_unfolding,[],[f45,f56])).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f46,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f50,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f50,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f49,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f46,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f108,plain,
    ( k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl5_7
  <=> k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f71,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f109,plain,
    ( ~ spl5_1
    | ~ spl5_4
    | spl5_6
    | spl5_7
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f101,f94,f106,f103,f89,f74])).

fof(f74,plain,
    ( spl5_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f89,plain,
    ( spl5_4
  <=> v1_funct_2(sK3,sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f94,plain,
    ( spl5_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f101,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
        | ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK3,X0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
        | ~ v1_funct_2(sK3,sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
        | ~ v1_funct_1(sK3) )
    | ~ spl5_5 ),
    inference(resolution,[],[f32,f96])).

fof(f96,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f94])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | r2_hidden(k1_funct_1(X3,X2),X1)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

fof(f97,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f57,f94])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) ),
    inference(definition_unfolding,[],[f29,f56])).

fof(f29,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( sK1 != k1_funct_1(sK3,sK2)
    & r2_hidden(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_2(sK3,sK0,k1_tarski(sK1))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( sK1 != k1_funct_1(sK3,sK2)
      & r2_hidden(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      & v1_funct_2(sK3,sK0,k1_tarski(sK1))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

fof(f92,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f58,f89])).

fof(f58,plain,(
    v1_funct_2(sK3,sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f28,f56])).

fof(f28,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f87,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f31,f84])).

fof(f31,plain,(
    sK1 != k1_funct_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f82,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f30,f79])).

fof(f30,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f77,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f27,f74])).

fof(f27,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:10:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (16513)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.52  % (16529)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.52  % (16514)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.53  % (16507)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (16517)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.53  % (16529)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (16527)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.53  % (16509)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.53  % (16507)Refutation not found, incomplete strategy% (16507)------------------------------
% 0.22/0.53  % (16507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (16506)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (16519)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.54  % (16520)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % (16508)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (16511)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (16533)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.54  % (16510)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (16507)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (16507)Memory used [KB]: 1663
% 0.22/0.54  % (16507)Time elapsed: 0.122 s
% 0.22/0.54  % (16507)------------------------------
% 0.22/0.54  % (16507)------------------------------
% 0.22/0.54  % (16512)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f134,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f77,f82,f87,f92,f97,f109,f120,f133])).
% 0.22/0.54  fof(f133,plain,(
% 0.22/0.54    ~spl5_2 | spl5_3 | ~spl5_6),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f128])).
% 0.22/0.54  fof(f128,plain,(
% 0.22/0.54    $false | (~spl5_2 | spl5_3 | ~spl5_6)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f81,f86,f127])).
% 0.22/0.54  fof(f127,plain,(
% 0.22/0.54    ( ! [X0] : (sK1 = k1_funct_1(sK3,X0) | ~r2_hidden(X0,sK0)) ) | ~spl5_6),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f126])).
% 0.22/0.54  fof(f126,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,sK0) | sK1 = k1_funct_1(sK3,X0) | sK1 = k1_funct_1(sK3,X0) | sK1 = k1_funct_1(sK3,X0) | sK1 = k1_funct_1(sK3,X0) | sK1 = k1_funct_1(sK3,X0)) ) | ~spl5_6),
% 0.22/0.54    inference(resolution,[],[f104,f70])).
% 0.22/0.54  fof(f70,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X7,X3,X1] : (~r2_hidden(X7,k3_enumset1(X0,X1,X2,X3,X4)) | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | X4 = X7) )),
% 0.22/0.54    inference(equality_resolution,[],[f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X7,X5,X3,X1] : (X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | ~r2_hidden(X7,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5) )),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | (((sK4(X0,X1,X2,X3,X4,X5) != X4 & sK4(X0,X1,X2,X3,X4,X5) != X3 & sK4(X0,X1,X2,X3,X4,X5) != X2 & sK4(X0,X1,X2,X3,X4,X5) != X1 & sK4(X0,X1,X2,X3,X4,X5) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3,X4,X5),X5)) & (sK4(X0,X1,X2,X3,X4,X5) = X4 | sK4(X0,X1,X2,X3,X4,X5) = X3 | sK4(X0,X1,X2,X3,X4,X5) = X2 | sK4(X0,X1,X2,X3,X4,X5) = X1 | sK4(X0,X1,X2,X3,X4,X5) = X0 | r2_hidden(sK4(X0,X1,X2,X3,X4,X5),X5)))) & (! [X7] : ((r2_hidden(X7,X5) | (X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & (X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | ~r2_hidden(X7,X5))) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X5,X4,X3,X2,X1,X0] : (? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | r2_hidden(X6,X5))) => (((sK4(X0,X1,X2,X3,X4,X5) != X4 & sK4(X0,X1,X2,X3,X4,X5) != X3 & sK4(X0,X1,X2,X3,X4,X5) != X2 & sK4(X0,X1,X2,X3,X4,X5) != X1 & sK4(X0,X1,X2,X3,X4,X5) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3,X4,X5),X5)) & (sK4(X0,X1,X2,X3,X4,X5) = X4 | sK4(X0,X1,X2,X3,X4,X5) = X3 | sK4(X0,X1,X2,X3,X4,X5) = X2 | sK4(X0,X1,X2,X3,X4,X5) = X1 | sK4(X0,X1,X2,X3,X4,X5) = X0 | r2_hidden(sK4(X0,X1,X2,X3,X4,X5),X5))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | r2_hidden(X6,X5)))) & (! [X7] : ((r2_hidden(X7,X5) | (X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & (X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | ~r2_hidden(X7,X5))) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 0.22/0.54    inference(rectify,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X5))) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 0.22/0.54    inference(flattening,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | ~r2_hidden(X6,X5))) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 0.22/0.54    inference(nnf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> ~(X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).
% 0.22/0.54  fof(f104,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~r2_hidden(X0,sK0)) ) | ~spl5_6),
% 0.22/0.54    inference(avatar_component_clause,[],[f103])).
% 0.22/0.54  fof(f103,plain,(
% 0.22/0.54    spl5_6 <=> ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK3,X0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    sK1 != k1_funct_1(sK3,sK2) | spl5_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f84])).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    spl5_3 <=> sK1 = k1_funct_1(sK3,sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.54  fof(f81,plain,(
% 0.22/0.54    r2_hidden(sK2,sK0) | ~spl5_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f79])).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    spl5_2 <=> r2_hidden(sK2,sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.54  fof(f120,plain,(
% 0.22/0.54    ~spl5_7),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f110])).
% 0.22/0.54  fof(f110,plain,(
% 0.22/0.54    $false | ~spl5_7),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f71,f108,f99])).
% 0.22/0.54  fof(f99,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_xboole_0 != X1 | ~r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)) )),
% 0.22/0.54    inference(superposition,[],[f59,f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.54  % (16525)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f45,f56])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f46,f55])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f49,f54])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f50,f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.22/0.54  fof(f108,plain,(
% 0.22/0.54    k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) | ~spl5_7),
% 0.22/0.54    inference(avatar_component_clause,[],[f106])).
% 0.22/0.54  fof(f106,plain,(
% 0.22/0.54    spl5_7 <=> k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.54    inference(equality_resolution,[],[f52])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(flattening,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.54  fof(f109,plain,(
% 0.22/0.54    ~spl5_1 | ~spl5_4 | spl5_6 | spl5_7 | ~spl5_5),
% 0.22/0.54    inference(avatar_split_clause,[],[f101,f94,f106,f103,f89,f74])).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    spl5_1 <=> v1_funct_1(sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.54  fof(f89,plain,(
% 0.22/0.54    spl5_4 <=> v1_funct_2(sK3,sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.54  fof(f94,plain,(
% 0.22/0.54    spl5_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.54  fof(f101,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) | ~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK3,X0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~v1_funct_2(sK3,sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~v1_funct_1(sK3)) ) | ~spl5_5),
% 0.22/0.54    inference(resolution,[],[f32,f96])).
% 0.22/0.54  fof(f96,plain,(
% 0.22/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) | ~spl5_5),
% 0.22/0.54    inference(avatar_component_clause,[],[f94])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | r2_hidden(k1_funct_1(X3,X2),X1) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.54    inference(flattening,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).
% 0.22/0.54  fof(f97,plain,(
% 0.22/0.54    spl5_5),
% 0.22/0.54    inference(avatar_split_clause,[],[f57,f94])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))))),
% 0.22/0.54    inference(definition_unfolding,[],[f29,f56])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 0.22/0.54    inference(flattening,[],[f12])).
% 0.22/0.54  fof(f12,plain,(
% 0.22/0.54    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 0.22/0.54    inference(ennf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 0.22/0.54    inference(negated_conjecture,[],[f10])).
% 0.22/0.54  fof(f10,conjecture,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).
% 0.22/0.54  fof(f92,plain,(
% 0.22/0.54    spl5_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f58,f89])).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    v1_funct_2(sK3,sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 0.22/0.54    inference(definition_unfolding,[],[f28,f56])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f87,plain,(
% 0.22/0.54    ~spl5_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f31,f84])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    sK1 != k1_funct_1(sK3,sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f82,plain,(
% 0.22/0.54    spl5_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f30,f79])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    r2_hidden(sK2,sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f77,plain,(
% 0.22/0.54    spl5_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f27,f74])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    v1_funct_1(sK3)),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (16529)------------------------------
% 0.22/0.54  % (16529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (16529)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (16529)Memory used [KB]: 10746
% 0.22/0.54  % (16529)Time elapsed: 0.122 s
% 0.22/0.54  % (16529)------------------------------
% 0.22/0.54  % (16529)------------------------------
% 0.22/0.54  % (16505)Success in time 0.179 s
%------------------------------------------------------------------------------
