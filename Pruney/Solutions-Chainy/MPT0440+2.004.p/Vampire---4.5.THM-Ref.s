%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:57 EST 2020

% Result     : Theorem 13.82s
% Output     : Refutation 13.82s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 467 expanded)
%              Number of leaves         :   23 ( 140 expanded)
%              Depth                    :   20
%              Number of atoms          :  343 (1774 expanded)
%              Number of equality atoms :  178 ( 919 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13825,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f131,f780,f13768,f13824])).

fof(f13824,plain,(
    ~ spl12_15 ),
    inference(avatar_contradiction_clause,[],[f13823])).

fof(f13823,plain,
    ( $false
    | ~ spl12_15 ),
    inference(equality_resolution,[],[f13822])).

fof(f13822,plain,
    ( ! [X1] : sK1 != X1
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f13821,f779])).

fof(f779,plain,
    ( ! [X8] : k2_relat_1(sK2) != k1_tarski(X8)
    | ~ spl12_15 ),
    inference(avatar_component_clause,[],[f778])).

fof(f778,plain,
    ( spl12_15
  <=> ! [X8] : k2_relat_1(sK2) != k1_tarski(X8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_15])])).

fof(f13821,plain,
    ( ! [X1] :
        ( sK1 != X1
        | k1_tarski(X1) = k2_relat_1(sK2) )
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f13820,f620])).

fof(f620,plain,(
    k1_xboole_0 != k2_relat_1(sK2) ),
    inference(superposition,[],[f64,f170])).

fof(f170,plain,(
    k2_relat_1(sK2) = k2_xboole_0(k1_tarski(sK1),k2_relat_1(sK2)) ),
    inference(resolution,[],[f159,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(f159,plain,(
    r2_hidden(sK1,k2_relat_1(sK2)) ),
    inference(resolution,[],[f148,f110])).

fof(f110,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X6,X5),X0)
      | r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f38,f41,f40,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f148,plain,(
    r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(superposition,[],[f113,f61])).

fof(f61,plain,(
    sK2 = k1_tarski(k4_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( k1_tarski(sK1) != k2_relat_1(sK2)
      | k1_tarski(sK0) != k1_relat_1(sK2) )
    & sK2 = k1_tarski(k4_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_tarski(X1) != k2_relat_1(X2)
          | k1_tarski(X0) != k1_relat_1(X2) )
        & k1_tarski(k4_tarski(X0,X1)) = X2 )
   => ( ( k1_tarski(sK1) != k2_relat_1(sK2)
        | k1_tarski(sK0) != k1_relat_1(sK2) )
      & sK2 = k1_tarski(k4_tarski(sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ( k1_tarski(X1) != k2_relat_1(X2)
        | k1_tarski(X0) != k1_relat_1(X2) )
      & k1_tarski(k4_tarski(X0,X1)) = X2 ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ~ ! [X0,X1,X2] :
        ( k1_tarski(k4_tarski(X0,X1)) = X2
       => ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_tarski(X0) = k1_relat_1(X2) ) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( k1_tarski(k4_tarski(X0,X1)) = X2
         => ( k1_tarski(X1) = k2_relat_1(X2)
            & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( k1_tarski(k4_tarski(X0,X1)) = X2
       => ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relat_1)).

fof(f113,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f112])).

fof(f112,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK9(X0,X1) != X0
            | ~ r2_hidden(sK9(X0,X1),X1) )
          & ( sK9(X0,X1) = X0
            | r2_hidden(sK9(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f44,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK9(X0,X1) != X0
          | ~ r2_hidden(sK9(X0,X1),X1) )
        & ( sK9(X0,X1) = X0
          | r2_hidden(sK9(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f13820,plain,
    ( ! [X1] :
        ( sK1 != X1
        | k1_xboole_0 = k2_relat_1(sK2)
        | k1_tarski(X1) = k2_relat_1(sK2) )
    | ~ spl12_15 ),
    inference(superposition,[],[f85,f13761])).

fof(f13761,plain,
    ( ! [X22] : sK1 = sK10(k2_relat_1(sK2),X22)
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f13760,f779])).

fof(f13760,plain,(
    ! [X22] :
      ( k2_relat_1(sK2) = k1_tarski(X22)
      | sK1 = sK10(k2_relat_1(sK2),X22) ) ),
    inference(subsumption_resolution,[],[f13749,f620])).

fof(f13749,plain,(
    ! [X22] :
      ( k1_xboole_0 = k2_relat_1(sK2)
      | k2_relat_1(sK2) = k1_tarski(X22)
      | sK1 = sK10(k2_relat_1(sK2),X22) ) ),
    inference(resolution,[],[f84,f631])).

fof(f631,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k2_relat_1(sK2))
      | sK1 = X2 ) ),
    inference(resolution,[],[f627,f111])).

fof(f111,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f627,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
      | sK1 = X1 ) ),
    inference(superposition,[],[f342,f61])).

fof(f342,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k1_tarski(k4_tarski(X2,X3)))
      | X1 = X3 ) ),
    inference(backward_demodulation,[],[f102,f67])).

fof(f67,plain,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_zfmisc_1)).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
        | X1 != X3
        | X0 != X2 )
      & ( ( X1 = X3
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
        | X1 != X3
        | X0 != X2 )
      & ( ( X1 = X3
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
    <=> ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_zfmisc_1)).

fof(f84,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK10(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( sK10(X0,X1) != X1
        & r2_hidden(sK10(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f26,f48])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK10(X0,X1) != X1
        & r2_hidden(sK10(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f85,plain,(
    ! [X0,X1] :
      ( sK10(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f13768,plain,(
    spl12_1 ),
    inference(avatar_contradiction_clause,[],[f13767])).

fof(f13767,plain,
    ( $false
    | spl12_1 ),
    inference(equality_resolution,[],[f13766])).

fof(f13766,plain,
    ( ! [X1] : sK0 != X1
    | spl12_1 ),
    inference(subsumption_resolution,[],[f13765,f783])).

fof(f783,plain,
    ( ! [X9] : k1_relat_1(sK2) != k1_tarski(X9)
    | spl12_1 ),
    inference(subsumption_resolution,[],[f782,f642])).

fof(f642,plain,(
    k1_xboole_0 != k1_relat_1(sK2) ),
    inference(superposition,[],[f64,f173])).

fof(f173,plain,(
    k1_relat_1(sK2) = k2_xboole_0(k1_tarski(sK0),k1_relat_1(sK2)) ),
    inference(resolution,[],[f160,f69])).

fof(f160,plain,(
    r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(resolution,[],[f148,f108])).

fof(f108,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f32,f35,f34,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f782,plain,
    ( ! [X9] :
        ( k1_relat_1(sK2) != k1_tarski(X9)
        | k1_xboole_0 = k1_relat_1(sK2) )
    | spl12_1 ),
    inference(subsumption_resolution,[],[f781,f126])).

fof(f126,plain,
    ( k1_tarski(sK0) != k1_relat_1(sK2)
    | spl12_1 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl12_1
  <=> k1_tarski(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f781,plain,(
    ! [X9] :
      ( k1_relat_1(sK2) != k1_tarski(X9)
      | k1_tarski(sK0) = k1_relat_1(sK2)
      | k1_xboole_0 = k1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f774,f456])).

fof(f456,plain,(
    ! [X0] : k1_tarski(X0) != k1_xboole_0 ),
    inference(superposition,[],[f64,f63])).

fof(f63,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f774,plain,(
    ! [X9] :
      ( k1_relat_1(sK2) != k1_tarski(X9)
      | k1_xboole_0 = k1_tarski(sK0)
      | k1_tarski(sK0) = k1_relat_1(sK2)
      | k1_xboole_0 = k1_relat_1(sK2) ) ),
    inference(superposition,[],[f100,f173])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) != k2_xboole_0(X1,X2)
      | k1_xboole_0 = X1
      | X1 = X2
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f13765,plain,
    ( ! [X1] :
        ( sK0 != X1
        | k1_tarski(X1) = k1_relat_1(sK2) )
    | spl12_1 ),
    inference(subsumption_resolution,[],[f13764,f642])).

fof(f13764,plain,
    ( ! [X1] :
        ( sK0 != X1
        | k1_xboole_0 = k1_relat_1(sK2)
        | k1_tarski(X1) = k1_relat_1(sK2) )
    | spl12_1 ),
    inference(superposition,[],[f85,f13759])).

fof(f13759,plain,
    ( ! [X21] : sK0 = sK10(k1_relat_1(sK2),X21)
    | spl12_1 ),
    inference(subsumption_resolution,[],[f13758,f783])).

fof(f13758,plain,(
    ! [X21] :
      ( k1_relat_1(sK2) = k1_tarski(X21)
      | sK0 = sK10(k1_relat_1(sK2),X21) ) ),
    inference(subsumption_resolution,[],[f13748,f642])).

fof(f13748,plain,(
    ! [X21] :
      ( k1_xboole_0 = k1_relat_1(sK2)
      | k1_relat_1(sK2) = k1_tarski(X21)
      | sK0 = sK10(k1_relat_1(sK2),X21) ) ),
    inference(resolution,[],[f84,f603])).

fof(f603,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_relat_1(sK2))
      | sK0 = X3 ) ),
    inference(resolution,[],[f403,f109])).

fof(f109,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f403,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
      | sK0 = X0 ) ),
    inference(superposition,[],[f341,f61])).

fof(f341,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k1_tarski(k4_tarski(X2,X3)))
      | X0 = X2 ) ),
    inference(backward_demodulation,[],[f101,f67])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f780,plain,
    ( spl12_2
    | spl12_15 ),
    inference(avatar_split_clause,[],[f776,f778,f128])).

fof(f128,plain,
    ( spl12_2
  <=> k1_tarski(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f776,plain,(
    ! [X8] :
      ( k2_relat_1(sK2) != k1_tarski(X8)
      | k1_tarski(sK1) = k2_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f775,f620])).

fof(f775,plain,(
    ! [X8] :
      ( k2_relat_1(sK2) != k1_tarski(X8)
      | k1_tarski(sK1) = k2_relat_1(sK2)
      | k1_xboole_0 = k2_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f773,f456])).

fof(f773,plain,(
    ! [X8] :
      ( k2_relat_1(sK2) != k1_tarski(X8)
      | k1_xboole_0 = k1_tarski(sK1)
      | k1_tarski(sK1) = k2_relat_1(sK2)
      | k1_xboole_0 = k2_relat_1(sK2) ) ),
    inference(superposition,[],[f100,f170])).

fof(f131,plain,
    ( ~ spl12_1
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f62,f128,f124])).

fof(f62,plain,
    ( k1_tarski(sK1) != k2_relat_1(sK2)
    | k1_tarski(sK0) != k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:28:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.49  % (21752)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.49  % (21760)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.49  % (21765)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.49  % (21757)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.51  % (21775)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.51  % (21761)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.51  % (21776)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (21759)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.51  % (21754)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (21777)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.52  % (21773)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.52  % (21767)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.53  % (21769)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.53  % (21766)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.53  % (21750)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (21778)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.53  % (21753)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (21751)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (21762)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.54  % (21764)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.54  % (21774)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (21756)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (21770)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (21779)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.55  % (21771)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.55  % (21772)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.55  % (21758)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.55  % (21779)Refutation not found, incomplete strategy% (21779)------------------------------
% 0.20/0.55  % (21779)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (21779)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (21779)Memory used [KB]: 1663
% 0.20/0.55  % (21779)Time elapsed: 0.112 s
% 0.20/0.55  % (21779)------------------------------
% 0.20/0.55  % (21779)------------------------------
% 0.20/0.55  % (21763)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.52/0.56  % (21755)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.52/0.56  % (21766)Refutation not found, incomplete strategy% (21766)------------------------------
% 1.52/0.56  % (21766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.56  % (21766)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.56  
% 1.52/0.56  % (21766)Memory used [KB]: 10746
% 1.52/0.56  % (21766)Time elapsed: 0.156 s
% 1.52/0.56  % (21766)------------------------------
% 1.52/0.56  % (21766)------------------------------
% 1.68/0.58  % (21768)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 2.40/0.67  % (21753)Refutation not found, incomplete strategy% (21753)------------------------------
% 2.40/0.67  % (21753)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.40/0.67  % (21753)Termination reason: Refutation not found, incomplete strategy
% 2.40/0.67  
% 2.40/0.67  % (21753)Memory used [KB]: 6140
% 2.40/0.67  % (21753)Time elapsed: 0.278 s
% 2.40/0.67  % (21753)------------------------------
% 2.40/0.67  % (21753)------------------------------
% 2.40/0.70  % (21782)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.76/0.74  % (21781)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.95/0.81  % (21752)Time limit reached!
% 2.95/0.81  % (21752)------------------------------
% 2.95/0.81  % (21752)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.95/0.81  % (21752)Termination reason: Time limit
% 2.95/0.81  
% 2.95/0.81  % (21752)Memory used [KB]: 6908
% 2.95/0.81  % (21752)Time elapsed: 0.406 s
% 2.95/0.81  % (21752)------------------------------
% 2.95/0.81  % (21752)------------------------------
% 3.49/0.85  % (21783)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 3.81/0.89  % (21774)Time limit reached!
% 3.81/0.89  % (21774)------------------------------
% 3.81/0.89  % (21774)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.81/0.89  % (21774)Termination reason: Time limit
% 3.81/0.89  % (21774)Termination phase: Saturation
% 3.81/0.89  
% 3.81/0.89  % (21774)Memory used [KB]: 18166
% 3.81/0.89  % (21774)Time elapsed: 0.400 s
% 3.81/0.89  % (21774)------------------------------
% 3.81/0.89  % (21774)------------------------------
% 3.81/0.89  % (21756)Time limit reached!
% 3.81/0.89  % (21756)------------------------------
% 3.81/0.89  % (21756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.81/0.89  % (21756)Termination reason: Time limit
% 3.81/0.89  % (21756)Termination phase: Saturation
% 3.81/0.89  
% 3.81/0.89  % (21756)Memory used [KB]: 16119
% 3.81/0.89  % (21756)Time elapsed: 0.502 s
% 3.81/0.89  % (21756)------------------------------
% 3.81/0.89  % (21756)------------------------------
% 3.81/0.90  % (21764)Time limit reached!
% 3.81/0.90  % (21764)------------------------------
% 3.81/0.90  % (21764)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.81/0.90  % (21764)Termination reason: Time limit
% 3.81/0.90  
% 3.81/0.90  % (21764)Memory used [KB]: 5373
% 3.81/0.90  % (21764)Time elapsed: 0.503 s
% 3.81/0.90  % (21764)------------------------------
% 3.81/0.90  % (21764)------------------------------
% 4.30/0.95  % (21784)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 4.44/1.02  % (21757)Time limit reached!
% 4.44/1.02  % (21757)------------------------------
% 4.44/1.02  % (21757)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.44/1.02  % (21785)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 4.44/1.02  % (21757)Termination reason: Time limit
% 4.44/1.02  
% 4.44/1.02  % (21757)Memory used [KB]: 5117
% 4.44/1.02  % (21757)Time elapsed: 0.612 s
% 4.44/1.02  % (21757)------------------------------
% 4.44/1.02  % (21757)------------------------------
% 4.78/1.03  % (21786)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 4.78/1.06  % (21787)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 6.64/1.22  % (21751)Time limit reached!
% 6.64/1.22  % (21751)------------------------------
% 6.64/1.22  % (21751)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.64/1.24  % (21751)Termination reason: Time limit
% 6.64/1.24  
% 6.64/1.24  % (21751)Memory used [KB]: 6652
% 6.64/1.24  % (21751)Time elapsed: 0.820 s
% 6.64/1.24  % (21751)------------------------------
% 6.64/1.24  % (21751)------------------------------
% 7.02/1.26  % (21788)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 7.72/1.39  % (21789)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 8.17/1.40  % (21762)Time limit reached!
% 8.17/1.40  % (21762)------------------------------
% 8.17/1.40  % (21762)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.17/1.40  % (21762)Termination reason: Time limit
% 8.17/1.40  
% 8.17/1.40  % (21762)Memory used [KB]: 14583
% 8.17/1.40  % (21762)Time elapsed: 1.001 s
% 8.17/1.40  % (21762)------------------------------
% 8.17/1.40  % (21762)------------------------------
% 8.17/1.41  % (21777)Time limit reached!
% 8.17/1.41  % (21777)------------------------------
% 8.17/1.41  % (21777)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.17/1.41  % (21777)Termination reason: Time limit
% 8.17/1.41  
% 8.17/1.41  % (21777)Memory used [KB]: 11385
% 8.17/1.41  % (21777)Time elapsed: 1.015 s
% 8.17/1.41  % (21777)------------------------------
% 8.17/1.41  % (21777)------------------------------
% 8.94/1.54  % (21791)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 9.26/1.55  % (21787)Time limit reached!
% 9.26/1.55  % (21787)------------------------------
% 9.26/1.55  % (21787)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.26/1.55  % (21787)Termination reason: Time limit
% 9.26/1.55  % (21787)Termination phase: Saturation
% 9.26/1.55  
% 9.26/1.55  % (21787)Memory used [KB]: 15607
% 9.26/1.55  % (21787)Time elapsed: 0.600 s
% 9.26/1.55  % (21787)------------------------------
% 9.26/1.55  % (21787)------------------------------
% 9.26/1.55  % (21783)Time limit reached!
% 9.26/1.55  % (21783)------------------------------
% 9.26/1.55  % (21783)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.26/1.55  % (21783)Termination reason: Time limit
% 9.26/1.55  
% 9.26/1.55  % (21783)Memory used [KB]: 14967
% 9.26/1.55  % (21783)Time elapsed: 0.819 s
% 9.26/1.55  % (21783)------------------------------
% 9.26/1.55  % (21783)------------------------------
% 9.26/1.56  % (21790)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 9.26/1.63  % (21750)Time limit reached!
% 9.26/1.63  % (21750)------------------------------
% 9.26/1.63  % (21750)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.26/1.63  % (21750)Termination reason: Time limit
% 9.26/1.63  
% 9.26/1.63  % (21750)Memory used [KB]: 3582
% 9.26/1.63  % (21750)Time elapsed: 1.230 s
% 9.26/1.63  % (21750)------------------------------
% 9.26/1.63  % (21750)------------------------------
% 9.93/1.69  % (21792)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 10.76/1.73  % (21755)Time limit reached!
% 10.76/1.73  % (21755)------------------------------
% 10.76/1.73  % (21755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.76/1.73  % (21755)Termination reason: Time limit
% 10.76/1.73  % (21755)Termination phase: Saturation
% 10.76/1.73  
% 10.76/1.73  % (21755)Memory used [KB]: 11769
% 10.76/1.73  % (21755)Time elapsed: 1.300 s
% 10.76/1.73  % (21755)------------------------------
% 10.76/1.73  % (21755)------------------------------
% 10.76/1.75  % (21793)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 10.76/1.77  % (21794)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 11.48/1.90  % (21795)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 12.87/2.04  % (21776)Time limit reached!
% 12.87/2.04  % (21776)------------------------------
% 12.87/2.04  % (21776)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.87/2.05  % (21776)Termination reason: Time limit
% 12.87/2.05  
% 12.87/2.05  % (21776)Memory used [KB]: 15735
% 12.87/2.05  % (21776)Time elapsed: 1.633 s
% 12.87/2.05  % (21776)------------------------------
% 12.87/2.05  % (21776)------------------------------
% 12.87/2.07  % (21794)Time limit reached!
% 12.87/2.07  % (21794)------------------------------
% 12.87/2.07  % (21794)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.87/2.07  % (21794)Termination reason: Time limit
% 12.87/2.07  
% 12.87/2.07  % (21794)Memory used [KB]: 15095
% 12.87/2.07  % (21794)Time elapsed: 0.416 s
% 12.87/2.07  % (21794)------------------------------
% 12.87/2.07  % (21794)------------------------------
% 13.82/2.16  % (21785)Refutation found. Thanks to Tanya!
% 13.82/2.16  % SZS status Theorem for theBenchmark
% 13.82/2.16  % SZS output start Proof for theBenchmark
% 13.82/2.16  fof(f13825,plain,(
% 13.82/2.16    $false),
% 13.82/2.16    inference(avatar_sat_refutation,[],[f131,f780,f13768,f13824])).
% 13.82/2.16  fof(f13824,plain,(
% 13.82/2.16    ~spl12_15),
% 13.82/2.16    inference(avatar_contradiction_clause,[],[f13823])).
% 13.82/2.16  fof(f13823,plain,(
% 13.82/2.16    $false | ~spl12_15),
% 13.82/2.16    inference(equality_resolution,[],[f13822])).
% 13.82/2.16  fof(f13822,plain,(
% 13.82/2.16    ( ! [X1] : (sK1 != X1) ) | ~spl12_15),
% 13.82/2.16    inference(subsumption_resolution,[],[f13821,f779])).
% 13.82/2.16  fof(f779,plain,(
% 13.82/2.16    ( ! [X8] : (k2_relat_1(sK2) != k1_tarski(X8)) ) | ~spl12_15),
% 13.82/2.16    inference(avatar_component_clause,[],[f778])).
% 13.82/2.16  fof(f778,plain,(
% 13.82/2.16    spl12_15 <=> ! [X8] : k2_relat_1(sK2) != k1_tarski(X8)),
% 13.82/2.16    introduced(avatar_definition,[new_symbols(naming,[spl12_15])])).
% 13.82/2.16  fof(f13821,plain,(
% 13.82/2.16    ( ! [X1] : (sK1 != X1 | k1_tarski(X1) = k2_relat_1(sK2)) ) | ~spl12_15),
% 13.82/2.16    inference(subsumption_resolution,[],[f13820,f620])).
% 13.82/2.16  fof(f620,plain,(
% 13.82/2.16    k1_xboole_0 != k2_relat_1(sK2)),
% 13.82/2.16    inference(superposition,[],[f64,f170])).
% 13.82/2.16  fof(f170,plain,(
% 13.82/2.16    k2_relat_1(sK2) = k2_xboole_0(k1_tarski(sK1),k2_relat_1(sK2))),
% 13.82/2.16    inference(resolution,[],[f159,f69])).
% 13.82/2.16  fof(f69,plain,(
% 13.82/2.16    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k2_xboole_0(k1_tarski(X0),X1) = X1) )),
% 13.82/2.16    inference(cnf_transformation,[],[f25])).
% 13.82/2.16  fof(f25,plain,(
% 13.82/2.16    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 13.82/2.16    inference(ennf_transformation,[],[f6])).
% 13.82/2.16  fof(f6,axiom,(
% 13.82/2.16    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 13.82/2.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).
% 13.82/2.16  fof(f159,plain,(
% 13.82/2.16    r2_hidden(sK1,k2_relat_1(sK2))),
% 13.82/2.16    inference(resolution,[],[f148,f110])).
% 13.82/2.16  fof(f110,plain,(
% 13.82/2.16    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X6,X5),X0) | r2_hidden(X5,k2_relat_1(X0))) )),
% 13.82/2.16    inference(equality_resolution,[],[f75])).
% 13.82/2.16  fof(f75,plain,(
% 13.82/2.16    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 13.82/2.16    inference(cnf_transformation,[],[f42])).
% 13.82/2.16  fof(f42,plain,(
% 13.82/2.16    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 13.82/2.16    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f38,f41,f40,f39])).
% 13.82/2.16  fof(f39,plain,(
% 13.82/2.16    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 13.82/2.16    introduced(choice_axiom,[])).
% 13.82/2.16  fof(f40,plain,(
% 13.82/2.16    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0) => r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0))),
% 13.82/2.16    introduced(choice_axiom,[])).
% 13.82/2.16  fof(f41,plain,(
% 13.82/2.16    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK8(X0,X5),X5),X0))),
% 13.82/2.16    introduced(choice_axiom,[])).
% 13.82/2.16  fof(f38,plain,(
% 13.82/2.16    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 13.82/2.16    inference(rectify,[],[f37])).
% 13.82/2.16  fof(f37,plain,(
% 13.82/2.16    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 13.82/2.16    inference(nnf_transformation,[],[f18])).
% 13.82/2.16  fof(f18,axiom,(
% 13.82/2.16    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 13.82/2.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 13.82/2.16  fof(f148,plain,(
% 13.82/2.16    r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 13.82/2.16    inference(superposition,[],[f113,f61])).
% 13.82/2.16  fof(f61,plain,(
% 13.82/2.16    sK2 = k1_tarski(k4_tarski(sK0,sK1))),
% 13.82/2.16    inference(cnf_transformation,[],[f30])).
% 13.82/2.16  fof(f30,plain,(
% 13.82/2.16    (k1_tarski(sK1) != k2_relat_1(sK2) | k1_tarski(sK0) != k1_relat_1(sK2)) & sK2 = k1_tarski(k4_tarski(sK0,sK1))),
% 13.82/2.16    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f29])).
% 13.82/2.16  fof(f29,plain,(
% 13.82/2.16    ? [X0,X1,X2] : ((k1_tarski(X1) != k2_relat_1(X2) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2) => ((k1_tarski(sK1) != k2_relat_1(sK2) | k1_tarski(sK0) != k1_relat_1(sK2)) & sK2 = k1_tarski(k4_tarski(sK0,sK1)))),
% 13.82/2.16    introduced(choice_axiom,[])).
% 13.82/2.16  fof(f23,plain,(
% 13.82/2.16    ? [X0,X1,X2] : ((k1_tarski(X1) != k2_relat_1(X2) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2)),
% 13.82/2.16    inference(ennf_transformation,[],[f22])).
% 13.82/2.16  fof(f22,plain,(
% 13.82/2.16    ~! [X0,X1,X2] : (k1_tarski(k4_tarski(X0,X1)) = X2 => (k1_tarski(X1) = k2_relat_1(X2) & k1_tarski(X0) = k1_relat_1(X2)))),
% 13.82/2.16    inference(pure_predicate_removal,[],[f20])).
% 13.82/2.16  fof(f20,negated_conjecture,(
% 13.82/2.16    ~! [X0,X1,X2] : (v1_relat_1(X2) => (k1_tarski(k4_tarski(X0,X1)) = X2 => (k1_tarski(X1) = k2_relat_1(X2) & k1_tarski(X0) = k1_relat_1(X2))))),
% 13.82/2.16    inference(negated_conjecture,[],[f19])).
% 13.82/2.16  fof(f19,conjecture,(
% 13.82/2.16    ! [X0,X1,X2] : (v1_relat_1(X2) => (k1_tarski(k4_tarski(X0,X1)) = X2 => (k1_tarski(X1) = k2_relat_1(X2) & k1_tarski(X0) = k1_relat_1(X2))))),
% 13.82/2.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relat_1)).
% 13.82/2.16  fof(f113,plain,(
% 13.82/2.16    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 13.82/2.16    inference(equality_resolution,[],[f112])).
% 13.82/2.16  fof(f112,plain,(
% 13.82/2.16    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 13.82/2.16    inference(equality_resolution,[],[f79])).
% 13.82/2.16  fof(f79,plain,(
% 13.82/2.16    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 13.82/2.16    inference(cnf_transformation,[],[f46])).
% 13.82/2.16  fof(f46,plain,(
% 13.82/2.16    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK9(X0,X1) != X0 | ~r2_hidden(sK9(X0,X1),X1)) & (sK9(X0,X1) = X0 | r2_hidden(sK9(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 13.82/2.16    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f44,f45])).
% 13.82/2.16  fof(f45,plain,(
% 13.82/2.16    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK9(X0,X1) != X0 | ~r2_hidden(sK9(X0,X1),X1)) & (sK9(X0,X1) = X0 | r2_hidden(sK9(X0,X1),X1))))),
% 13.82/2.16    introduced(choice_axiom,[])).
% 13.82/2.16  fof(f44,plain,(
% 13.82/2.16    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 13.82/2.16    inference(rectify,[],[f43])).
% 13.82/2.16  fof(f43,plain,(
% 13.82/2.16    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 13.82/2.16    inference(nnf_transformation,[],[f4])).
% 13.82/2.16  fof(f4,axiom,(
% 13.82/2.16    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 13.82/2.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 13.82/2.16  fof(f64,plain,(
% 13.82/2.16    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 13.82/2.16    inference(cnf_transformation,[],[f14])).
% 13.82/2.16  fof(f14,axiom,(
% 13.82/2.16    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 13.82/2.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 13.82/2.16  fof(f13820,plain,(
% 13.82/2.16    ( ! [X1] : (sK1 != X1 | k1_xboole_0 = k2_relat_1(sK2) | k1_tarski(X1) = k2_relat_1(sK2)) ) | ~spl12_15),
% 13.82/2.16    inference(superposition,[],[f85,f13761])).
% 13.82/2.16  fof(f13761,plain,(
% 13.82/2.16    ( ! [X22] : (sK1 = sK10(k2_relat_1(sK2),X22)) ) | ~spl12_15),
% 13.82/2.16    inference(subsumption_resolution,[],[f13760,f779])).
% 13.82/2.16  fof(f13760,plain,(
% 13.82/2.16    ( ! [X22] : (k2_relat_1(sK2) = k1_tarski(X22) | sK1 = sK10(k2_relat_1(sK2),X22)) )),
% 13.82/2.16    inference(subsumption_resolution,[],[f13749,f620])).
% 13.82/2.16  fof(f13749,plain,(
% 13.82/2.16    ( ! [X22] : (k1_xboole_0 = k2_relat_1(sK2) | k2_relat_1(sK2) = k1_tarski(X22) | sK1 = sK10(k2_relat_1(sK2),X22)) )),
% 13.82/2.16    inference(resolution,[],[f84,f631])).
% 13.82/2.16  fof(f631,plain,(
% 13.82/2.16    ( ! [X2] : (~r2_hidden(X2,k2_relat_1(sK2)) | sK1 = X2) )),
% 13.82/2.16    inference(resolution,[],[f627,f111])).
% 13.82/2.16  fof(f111,plain,(
% 13.82/2.16    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 13.82/2.16    inference(equality_resolution,[],[f74])).
% 13.82/2.16  fof(f74,plain,(
% 13.82/2.16    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 13.82/2.16    inference(cnf_transformation,[],[f42])).
% 13.82/2.16  fof(f627,plain,(
% 13.82/2.16    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | sK1 = X1) )),
% 13.82/2.16    inference(superposition,[],[f342,f61])).
% 13.82/2.16  fof(f342,plain,(
% 13.82/2.16    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k1_tarski(k4_tarski(X2,X3))) | X1 = X3) )),
% 13.82/2.16    inference(backward_demodulation,[],[f102,f67])).
% 13.82/2.16  fof(f67,plain,(
% 13.82/2.16    ( ! [X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))) )),
% 13.82/2.16    inference(cnf_transformation,[],[f11])).
% 13.82/2.16  fof(f11,axiom,(
% 13.82/2.16    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))),
% 13.82/2.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_zfmisc_1)).
% 13.82/2.16  fof(f102,plain,(
% 13.82/2.16    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) | X1 = X3) )),
% 13.82/2.16    inference(cnf_transformation,[],[f60])).
% 13.82/2.16  fof(f60,plain,(
% 13.82/2.16    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) | X1 != X3 | X0 != X2) & ((X1 = X3 & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))))),
% 13.82/2.16    inference(flattening,[],[f59])).
% 13.82/2.18  fof(f59,plain,(
% 13.82/2.18    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) | (X1 != X3 | X0 != X2)) & ((X1 = X3 & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))))),
% 13.82/2.18    inference(nnf_transformation,[],[f10])).
% 13.82/2.18  fof(f10,axiom,(
% 13.82/2.18    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) <=> (X1 = X3 & X0 = X2))),
% 13.82/2.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_zfmisc_1)).
% 13.82/2.18  fof(f84,plain,(
% 13.82/2.18    ( ! [X0,X1] : (r2_hidden(sK10(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 13.82/2.18    inference(cnf_transformation,[],[f49])).
% 13.82/2.18  fof(f49,plain,(
% 13.82/2.18    ! [X0,X1] : ((sK10(X0,X1) != X1 & r2_hidden(sK10(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 13.82/2.18    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f26,f48])).
% 13.82/2.18  fof(f48,plain,(
% 13.82/2.18    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK10(X0,X1) != X1 & r2_hidden(sK10(X0,X1),X0)))),
% 13.82/2.18    introduced(choice_axiom,[])).
% 13.82/2.18  fof(f26,plain,(
% 13.82/2.18    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 13.82/2.18    inference(ennf_transformation,[],[f12])).
% 13.82/2.18  fof(f12,axiom,(
% 13.82/2.18    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 13.82/2.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 13.82/2.18  fof(f85,plain,(
% 13.82/2.18    ( ! [X0,X1] : (sK10(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 13.82/2.18    inference(cnf_transformation,[],[f49])).
% 13.82/2.18  fof(f13768,plain,(
% 13.82/2.18    spl12_1),
% 13.82/2.18    inference(avatar_contradiction_clause,[],[f13767])).
% 13.82/2.18  fof(f13767,plain,(
% 13.82/2.18    $false | spl12_1),
% 13.82/2.18    inference(equality_resolution,[],[f13766])).
% 13.82/2.18  fof(f13766,plain,(
% 13.82/2.18    ( ! [X1] : (sK0 != X1) ) | spl12_1),
% 13.82/2.18    inference(subsumption_resolution,[],[f13765,f783])).
% 13.82/2.18  fof(f783,plain,(
% 13.82/2.18    ( ! [X9] : (k1_relat_1(sK2) != k1_tarski(X9)) ) | spl12_1),
% 13.82/2.18    inference(subsumption_resolution,[],[f782,f642])).
% 13.82/2.18  fof(f642,plain,(
% 13.82/2.18    k1_xboole_0 != k1_relat_1(sK2)),
% 13.82/2.18    inference(superposition,[],[f64,f173])).
% 13.82/2.18  fof(f173,plain,(
% 13.82/2.18    k1_relat_1(sK2) = k2_xboole_0(k1_tarski(sK0),k1_relat_1(sK2))),
% 13.82/2.18    inference(resolution,[],[f160,f69])).
% 13.82/2.18  fof(f160,plain,(
% 13.82/2.18    r2_hidden(sK0,k1_relat_1(sK2))),
% 13.82/2.18    inference(resolution,[],[f148,f108])).
% 13.82/2.18  fof(f108,plain,(
% 13.82/2.18    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X5,X6),X0) | r2_hidden(X5,k1_relat_1(X0))) )),
% 13.82/2.18    inference(equality_resolution,[],[f71])).
% 13.82/2.18  fof(f71,plain,(
% 13.82/2.18    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 13.82/2.18    inference(cnf_transformation,[],[f36])).
% 13.82/2.18  fof(f36,plain,(
% 13.82/2.18    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 13.82/2.18    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f32,f35,f34,f33])).
% 13.82/2.18  fof(f33,plain,(
% 13.82/2.18    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 13.82/2.18    introduced(choice_axiom,[])).
% 13.82/2.18  fof(f34,plain,(
% 13.82/2.18    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0))),
% 13.82/2.18    introduced(choice_axiom,[])).
% 13.82/2.18  fof(f35,plain,(
% 13.82/2.18    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0))),
% 13.82/2.18    introduced(choice_axiom,[])).
% 13.82/2.18  fof(f32,plain,(
% 13.82/2.18    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 13.82/2.18    inference(rectify,[],[f31])).
% 13.82/2.18  fof(f31,plain,(
% 13.82/2.18    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 13.82/2.18    inference(nnf_transformation,[],[f17])).
% 13.82/2.18  fof(f17,axiom,(
% 13.82/2.18    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 13.82/2.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 13.82/2.18  fof(f782,plain,(
% 13.82/2.18    ( ! [X9] : (k1_relat_1(sK2) != k1_tarski(X9) | k1_xboole_0 = k1_relat_1(sK2)) ) | spl12_1),
% 13.82/2.18    inference(subsumption_resolution,[],[f781,f126])).
% 13.82/2.18  fof(f126,plain,(
% 13.82/2.18    k1_tarski(sK0) != k1_relat_1(sK2) | spl12_1),
% 13.82/2.18    inference(avatar_component_clause,[],[f124])).
% 13.82/2.18  fof(f124,plain,(
% 13.82/2.18    spl12_1 <=> k1_tarski(sK0) = k1_relat_1(sK2)),
% 13.82/2.18    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 13.82/2.18  fof(f781,plain,(
% 13.82/2.18    ( ! [X9] : (k1_relat_1(sK2) != k1_tarski(X9) | k1_tarski(sK0) = k1_relat_1(sK2) | k1_xboole_0 = k1_relat_1(sK2)) )),
% 13.82/2.18    inference(subsumption_resolution,[],[f774,f456])).
% 13.82/2.18  fof(f456,plain,(
% 13.82/2.18    ( ! [X0] : (k1_tarski(X0) != k1_xboole_0) )),
% 13.82/2.18    inference(superposition,[],[f64,f63])).
% 13.82/2.18  fof(f63,plain,(
% 13.82/2.18    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 13.82/2.18    inference(cnf_transformation,[],[f21])).
% 13.82/2.18  fof(f21,plain,(
% 13.82/2.18    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 13.82/2.18    inference(rectify,[],[f3])).
% 13.82/2.18  fof(f3,axiom,(
% 13.82/2.18    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 13.82/2.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 13.82/2.18  fof(f774,plain,(
% 13.82/2.18    ( ! [X9] : (k1_relat_1(sK2) != k1_tarski(X9) | k1_xboole_0 = k1_tarski(sK0) | k1_tarski(sK0) = k1_relat_1(sK2) | k1_xboole_0 = k1_relat_1(sK2)) )),
% 13.82/2.18    inference(superposition,[],[f100,f173])).
% 13.82/2.18  fof(f100,plain,(
% 13.82/2.18    ( ! [X2,X0,X1] : (k1_tarski(X0) != k2_xboole_0(X1,X2) | k1_xboole_0 = X1 | X1 = X2 | k1_xboole_0 = X2) )),
% 13.82/2.18    inference(cnf_transformation,[],[f28])).
% 13.82/2.18  fof(f28,plain,(
% 13.82/2.18    ! [X0,X1,X2] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k1_tarski(X0) != k2_xboole_0(X1,X2))),
% 13.82/2.18    inference(ennf_transformation,[],[f13])).
% 13.82/2.18  fof(f13,axiom,(
% 13.82/2.18    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 13.82/2.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 13.82/2.18  fof(f13765,plain,(
% 13.82/2.18    ( ! [X1] : (sK0 != X1 | k1_tarski(X1) = k1_relat_1(sK2)) ) | spl12_1),
% 13.82/2.18    inference(subsumption_resolution,[],[f13764,f642])).
% 13.82/2.18  fof(f13764,plain,(
% 13.82/2.18    ( ! [X1] : (sK0 != X1 | k1_xboole_0 = k1_relat_1(sK2) | k1_tarski(X1) = k1_relat_1(sK2)) ) | spl12_1),
% 13.82/2.18    inference(superposition,[],[f85,f13759])).
% 13.82/2.18  fof(f13759,plain,(
% 13.82/2.18    ( ! [X21] : (sK0 = sK10(k1_relat_1(sK2),X21)) ) | spl12_1),
% 13.82/2.18    inference(subsumption_resolution,[],[f13758,f783])).
% 13.82/2.18  fof(f13758,plain,(
% 13.82/2.18    ( ! [X21] : (k1_relat_1(sK2) = k1_tarski(X21) | sK0 = sK10(k1_relat_1(sK2),X21)) )),
% 13.82/2.18    inference(subsumption_resolution,[],[f13748,f642])).
% 13.82/2.18  fof(f13748,plain,(
% 13.82/2.18    ( ! [X21] : (k1_xboole_0 = k1_relat_1(sK2) | k1_relat_1(sK2) = k1_tarski(X21) | sK0 = sK10(k1_relat_1(sK2),X21)) )),
% 13.82/2.18    inference(resolution,[],[f84,f603])).
% 13.82/2.18  fof(f603,plain,(
% 13.82/2.18    ( ! [X3] : (~r2_hidden(X3,k1_relat_1(sK2)) | sK0 = X3) )),
% 13.82/2.18    inference(resolution,[],[f403,f109])).
% 13.82/2.18  fof(f109,plain,(
% 13.82/2.18    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 13.82/2.18    inference(equality_resolution,[],[f70])).
% 13.82/2.18  fof(f70,plain,(
% 13.82/2.18    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 13.82/2.18    inference(cnf_transformation,[],[f36])).
% 13.82/2.18  fof(f403,plain,(
% 13.82/2.18    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | sK0 = X0) )),
% 13.82/2.18    inference(superposition,[],[f341,f61])).
% 13.82/2.18  fof(f341,plain,(
% 13.82/2.18    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k1_tarski(k4_tarski(X2,X3))) | X0 = X2) )),
% 13.82/2.18    inference(backward_demodulation,[],[f101,f67])).
% 13.82/2.18  fof(f101,plain,(
% 13.82/2.18    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) | X0 = X2) )),
% 13.82/2.18    inference(cnf_transformation,[],[f60])).
% 13.82/2.18  fof(f780,plain,(
% 13.82/2.18    spl12_2 | spl12_15),
% 13.82/2.18    inference(avatar_split_clause,[],[f776,f778,f128])).
% 13.82/2.18  fof(f128,plain,(
% 13.82/2.18    spl12_2 <=> k1_tarski(sK1) = k2_relat_1(sK2)),
% 13.82/2.18    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 13.82/2.18  fof(f776,plain,(
% 13.82/2.18    ( ! [X8] : (k2_relat_1(sK2) != k1_tarski(X8) | k1_tarski(sK1) = k2_relat_1(sK2)) )),
% 13.82/2.18    inference(subsumption_resolution,[],[f775,f620])).
% 13.82/2.18  fof(f775,plain,(
% 13.82/2.18    ( ! [X8] : (k2_relat_1(sK2) != k1_tarski(X8) | k1_tarski(sK1) = k2_relat_1(sK2) | k1_xboole_0 = k2_relat_1(sK2)) )),
% 13.82/2.18    inference(subsumption_resolution,[],[f773,f456])).
% 13.82/2.18  fof(f773,plain,(
% 13.82/2.18    ( ! [X8] : (k2_relat_1(sK2) != k1_tarski(X8) | k1_xboole_0 = k1_tarski(sK1) | k1_tarski(sK1) = k2_relat_1(sK2) | k1_xboole_0 = k2_relat_1(sK2)) )),
% 13.82/2.18    inference(superposition,[],[f100,f170])).
% 13.82/2.18  fof(f131,plain,(
% 13.82/2.18    ~spl12_1 | ~spl12_2),
% 13.82/2.18    inference(avatar_split_clause,[],[f62,f128,f124])).
% 13.82/2.18  fof(f62,plain,(
% 13.82/2.18    k1_tarski(sK1) != k2_relat_1(sK2) | k1_tarski(sK0) != k1_relat_1(sK2)),
% 13.82/2.18    inference(cnf_transformation,[],[f30])).
% 13.82/2.18  % SZS output end Proof for theBenchmark
% 13.82/2.18  % (21785)------------------------------
% 13.82/2.18  % (21785)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.82/2.18  % (21785)Termination reason: Refutation
% 13.82/2.18  
% 13.82/2.18  % (21785)Memory used [KB]: 24178
% 13.82/2.18  % (21785)Time elapsed: 1.249 s
% 13.82/2.18  % (21785)------------------------------
% 13.82/2.18  % (21785)------------------------------
% 13.82/2.19  % (21749)Success in time 1.821 s
%------------------------------------------------------------------------------
