%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:59 EST 2020

% Result     : Theorem 19.54s
% Output     : Refutation 20.46s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 382 expanded)
%              Number of leaves         :   24 ( 142 expanded)
%              Depth                    :   12
%              Number of atoms          :  400 (1442 expanded)
%              Number of equality atoms :  106 ( 405 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (23887)Time limit reached!
% (23887)------------------------------
% (23887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23887)Termination reason: Time limit

% (23887)Memory used [KB]: 7291
% (23887)Time elapsed: 0.424 s
% (23887)------------------------------
% (23887)------------------------------
fof(f24176,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f71,f101,f1131,f1477,f1555,f13355,f23841,f23974,f24130,f24135,f24173])).

fof(f24173,plain,
    ( spl9_2
    | ~ spl9_3
    | ~ spl9_7
    | ~ spl9_467 ),
    inference(avatar_contradiction_clause,[],[f24172])).

fof(f24172,plain,
    ( $false
    | spl9_2
    | ~ spl9_3
    | ~ spl9_7
    | ~ spl9_467 ),
    inference(subsumption_resolution,[],[f24171,f65])).

fof(f65,plain,
    ( k1_tarski(sK1) != k2_relat_1(sK2)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl9_2
  <=> k1_tarski(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f24171,plain,
    ( k1_tarski(sK1) = k2_relat_1(sK2)
    | ~ spl9_3
    | ~ spl9_7
    | ~ spl9_467 ),
    inference(subsumption_resolution,[],[f24170,f191])).

fof(f191,plain,
    ( ! [X0] : r2_hidden(X0,k1_tarski(X0))
    | ~ spl9_3 ),
    inference(resolution,[],[f108,f75])).

fof(f75,plain,
    ( ! [X0] : r2_hidden(k4_tarski(X0,k4_tarski(sK0,sK1)),k2_zfmisc_1(k1_tarski(X0),sK2))
    | ~ spl9_3 ),
    inference(superposition,[],[f56,f70])).

fof(f70,plain,
    ( sK2 = k1_tarski(k4_tarski(sK0,sK1))
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl9_3
  <=> sK2 = k1_tarski(k4_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f56,plain,(
    ! [X2,X3] : r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
      | X0 != X2 ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
      | X1 != X3
      | X0 != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
        | X1 != X3
        | X0 != X2 )
      & ( ( X1 = X3
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
        | X1 != X3
        | X0 != X2 )
      & ( ( X1 = X3
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
    <=> ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_zfmisc_1)).

fof(f108,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,sK2))
        | r2_hidden(X0,X2) )
    | ~ spl9_3 ),
    inference(superposition,[],[f44,f70])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(f24170,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | k1_tarski(sK1) = k2_relat_1(sK2)
    | ~ spl9_7
    | ~ spl9_467 ),
    inference(subsumption_resolution,[],[f24167,f105])).

fof(f105,plain,
    ( r2_hidden(sK1,k2_relat_1(sK2))
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl9_7
  <=> r2_hidden(sK1,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f24167,plain,
    ( ~ r2_hidden(sK1,k2_relat_1(sK2))
    | ~ r2_hidden(sK1,k1_tarski(sK1))
    | k1_tarski(sK1) = k2_relat_1(sK2)
    | ~ spl9_467 ),
    inference(superposition,[],[f152,f23840])).

fof(f23840,plain,
    ( sK1 = sK3(sK2,k1_tarski(sK1))
    | ~ spl9_467 ),
    inference(avatar_component_clause,[],[f23838])).

fof(f23838,plain,
    ( spl9_467
  <=> sK1 = sK3(sK2,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_467])])).

fof(f152,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),k2_relat_1(X0))
      | ~ r2_hidden(sK3(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(resolution,[],[f36,f52])).

fof(f52,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f16,f19,f18,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
      | k2_relat_1(X0) = X1
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f24135,plain,
    ( spl9_467
    | ~ spl9_3
    | ~ spl9_465 ),
    inference(avatar_split_clause,[],[f24133,f23750,f68,f23838])).

fof(f23750,plain,
    ( spl9_465
  <=> r2_hidden(sK3(sK2,k1_tarski(sK1)),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_465])])).

fof(f24133,plain,
    ( sK1 = sK3(sK2,k1_tarski(sK1))
    | ~ spl9_3
    | ~ spl9_465 ),
    inference(resolution,[],[f23752,f552])).

fof(f552,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X2,k1_tarski(X1))
        | X1 = X2 )
    | ~ spl9_3 ),
    inference(resolution,[],[f319,f237])).

fof(f237,plain,
    ( ! [X4,X5] :
        ( r2_hidden(X4,k1_relat_1(k2_zfmisc_1(X5,sK2)))
        | ~ r2_hidden(X4,X5) )
    | ~ spl9_3 ),
    inference(resolution,[],[f133,f53])).

fof(f53,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f22,f25,f24,f23])).

fof(f23,plain,(
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

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f133,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,k4_tarski(sK0,sK1)),k2_zfmisc_1(X1,sK2))
        | ~ r2_hidden(X0,X1) )
    | ~ spl9_3 ),
    inference(superposition,[],[f57,f70])).

fof(f57,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(X2,k1_tarski(X3)))
      | ~ r2_hidden(X0,X2) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
      | X1 != X3
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f319,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X4,k1_relat_1(k2_zfmisc_1(k1_tarski(X3),sK2)))
        | X3 = X4 )
    | ~ spl9_3 ),
    inference(superposition,[],[f150,f78])).

fof(f78,plain,
    ( ! [X0] : k2_zfmisc_1(k1_tarski(X0),sK2) = k1_tarski(k4_tarski(X0,k4_tarski(sK0,sK1)))
    | ~ spl9_3 ),
    inference(superposition,[],[f47,f70])).

fof(f47,plain,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).

fof(f150,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X4,k1_relat_1(k1_tarski(k4_tarski(X5,X6))))
      | X4 = X5 ) ),
    inference(resolution,[],[f135,f54])).

fof(f54,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f135,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k1_tarski(k4_tarski(X2,X3)))
      | X0 = X2 ) ),
    inference(forward_demodulation,[],[f41,f47])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f23752,plain,
    ( r2_hidden(sK3(sK2,k1_tarski(sK1)),k1_tarski(sK1))
    | ~ spl9_465 ),
    inference(avatar_component_clause,[],[f23750])).

fof(f24130,plain,
    ( spl9_465
    | spl9_2
    | spl9_468 ),
    inference(avatar_split_clause,[],[f24129,f23844,f63,f23750])).

fof(f23844,plain,
    ( spl9_468
  <=> r2_hidden(sK3(sK2,k1_tarski(sK1)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_468])])).

fof(f24129,plain,
    ( r2_hidden(sK3(sK2,k1_tarski(sK1)),k1_tarski(sK1))
    | spl9_2
    | spl9_468 ),
    inference(subsumption_resolution,[],[f24127,f65])).

fof(f24127,plain,
    ( r2_hidden(sK3(sK2,k1_tarski(sK1)),k1_tarski(sK1))
    | k1_tarski(sK1) = k2_relat_1(sK2)
    | spl9_468 ),
    inference(resolution,[],[f23845,f160])).

fof(f160,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK3(X4,X5),k2_relat_1(X4))
      | r2_hidden(sK3(X4,X5),X5)
      | k2_relat_1(X4) = X5 ) ),
    inference(resolution,[],[f35,f51])).

fof(f51,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X6,X5),X0)
      | r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
      | k2_relat_1(X0) = X1
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f23845,plain,
    ( ~ r2_hidden(sK3(sK2,k1_tarski(sK1)),k2_relat_1(sK2))
    | spl9_468 ),
    inference(avatar_component_clause,[],[f23844])).

fof(f23974,plain,
    ( ~ spl9_468
    | ~ spl9_3
    | spl9_466 ),
    inference(avatar_split_clause,[],[f23970,f23754,f68,f23844])).

fof(f23754,plain,
    ( spl9_466
  <=> r2_hidden(k4_tarski(sK0,sK3(sK2,k1_tarski(sK1))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_466])])).

fof(f23970,plain,
    ( ~ r2_hidden(sK3(sK2,k1_tarski(sK1)),k2_relat_1(sK2))
    | ~ spl9_3
    | spl9_466 ),
    inference(resolution,[],[f23755,f309])).

fof(f309,plain,
    ( ! [X1] :
        ( r2_hidden(k4_tarski(sK0,X1),sK2)
        | ~ r2_hidden(X1,k2_relat_1(sK2)) )
    | ~ spl9_3 ),
    inference(duplicate_literal_removal,[],[f308])).

fof(f308,plain,
    ( ! [X1] :
        ( r2_hidden(k4_tarski(sK0,X1),sK2)
        | ~ r2_hidden(X1,k2_relat_1(sK2))
        | ~ r2_hidden(X1,k2_relat_1(sK2)) )
    | ~ spl9_3 ),
    inference(superposition,[],[f52,f156])).

fof(f156,plain,
    ( ! [X0] :
        ( sK0 = sK5(sK2,X0)
        | ~ r2_hidden(X0,k2_relat_1(sK2)) )
    | ~ spl9_3 ),
    inference(resolution,[],[f151,f52])).

fof(f151,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | sK0 = X0 )
    | ~ spl9_3 ),
    inference(superposition,[],[f135,f70])).

fof(f23755,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK3(sK2,k1_tarski(sK1))),sK2)
    | spl9_466 ),
    inference(avatar_component_clause,[],[f23754])).

fof(f23841,plain,
    ( spl9_467
    | ~ spl9_3
    | ~ spl9_466 ),
    inference(avatar_split_clause,[],[f23824,f23754,f68,f23838])).

fof(f23824,plain,
    ( sK1 = sK3(sK2,k1_tarski(sK1))
    | ~ spl9_3
    | ~ spl9_466 ),
    inference(resolution,[],[f23756,f325])).

fof(f325,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | sK1 = X1 )
    | ~ spl9_3 ),
    inference(superposition,[],[f112,f70])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),k1_tarski(k4_tarski(X0,X1)))
      | X1 = X3 ) ),
    inference(superposition,[],[f45,f47])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f23756,plain,
    ( r2_hidden(k4_tarski(sK0,sK3(sK2,k1_tarski(sK1))),sK2)
    | ~ spl9_466 ),
    inference(avatar_component_clause,[],[f23754])).

fof(f13355,plain,
    ( spl9_5
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f13269,f68,f91])).

fof(f91,plain,
    ( spl9_5
  <=> r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f13269,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl9_3 ),
    inference(superposition,[],[f191,f70])).

fof(f1555,plain,
    ( spl9_7
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f1520,f68,f103])).

fof(f1520,plain,
    ( r2_hidden(sK1,k2_relat_1(sK2))
    | ~ spl9_3 ),
    inference(superposition,[],[f209,f70])).

fof(f209,plain,
    ( ! [X4,X3] : r2_hidden(X3,k2_relat_1(k1_tarski(k4_tarski(X4,X3))))
    | ~ spl9_3 ),
    inference(resolution,[],[f191,f51])).

fof(f1477,plain,
    ( spl9_1
    | ~ spl9_3
    | ~ spl9_6
    | ~ spl9_35 ),
    inference(avatar_split_clause,[],[f1467,f1117,f98,f68,f59])).

fof(f59,plain,
    ( spl9_1
  <=> k1_tarski(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f98,plain,
    ( spl9_6
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f1117,plain,
    ( spl9_35
  <=> sK0 = sK6(sK2,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).

fof(f1467,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK2)
    | ~ spl9_3
    | ~ spl9_6
    | ~ spl9_35 ),
    inference(subsumption_resolution,[],[f1466,f191])).

fof(f1466,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | k1_tarski(sK0) = k1_relat_1(sK2)
    | ~ spl9_6
    | ~ spl9_35 ),
    inference(subsumption_resolution,[],[f1463,f100])).

fof(f100,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f1463,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | k1_tarski(sK0) = k1_relat_1(sK2)
    | ~ spl9_35 ),
    inference(superposition,[],[f153,f1119])).

fof(f1119,plain,
    ( sK0 = sK6(sK2,k1_tarski(sK0))
    | ~ spl9_35 ),
    inference(avatar_component_clause,[],[f1117])).

fof(f153,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),k1_relat_1(X0))
      | ~ r2_hidden(sK6(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(resolution,[],[f40,f54])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
      | k1_relat_1(X0) = X1
      | ~ r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1131,plain,
    ( spl9_35
    | spl9_1
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f1130,f68,f59,f1117])).

fof(f1130,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK2)
    | sK0 = sK6(sK2,k1_tarski(sK0))
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f1099,f157])).

fof(f157,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK2))
        | sK0 = X1 )
    | ~ spl9_3 ),
    inference(resolution,[],[f151,f54])).

fof(f1099,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK2)
    | sK0 = sK6(sK2,k1_tarski(sK0))
    | r2_hidden(sK6(sK2,k1_tarski(sK0)),k1_relat_1(sK2))
    | ~ spl9_3 ),
    inference(resolution,[],[f172,f499])).

fof(f499,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_tarski(sK0))
        | r2_hidden(X3,k1_relat_1(sK2)) )
    | ~ spl9_3 ),
    inference(resolution,[],[f354,f53])).

fof(f354,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,sK1),sK2)
        | ~ r2_hidden(X0,k1_tarski(sK0)) )
    | ~ spl9_3 ),
    inference(superposition,[],[f134,f70])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,X1),k1_tarski(k4_tarski(X0,X1)))
      | ~ r2_hidden(X2,k1_tarski(X0)) ) ),
    inference(superposition,[],[f57,f47])).

fof(f172,plain,
    ( ! [X15] :
        ( r2_hidden(sK6(sK2,X15),X15)
        | k1_relat_1(sK2) = X15
        | sK0 = sK6(sK2,X15) )
    | ~ spl9_3 ),
    inference(resolution,[],[f39,f151])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
      | k1_relat_1(X0) = X1
      | r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f101,plain,
    ( spl9_6
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f95,f91,f98])).

fof(f95,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl9_5 ),
    inference(resolution,[],[f93,f53])).

fof(f93,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f91])).

fof(f71,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f31,f68])).

fof(f31,plain,(
    sK2 = k1_tarski(k4_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( k1_tarski(sK1) != k2_relat_1(sK2)
      | k1_tarski(sK0) != k1_relat_1(sK2) )
    & sK2 = k1_tarski(k4_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_tarski(X1) != k2_relat_1(X2)
          | k1_tarski(X0) != k1_relat_1(X2) )
        & k1_tarski(k4_tarski(X0,X1)) = X2 )
   => ( ( k1_tarski(sK1) != k2_relat_1(sK2)
        | k1_tarski(sK0) != k1_relat_1(sK2) )
      & sK2 = k1_tarski(k4_tarski(sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( k1_tarski(X1) != k2_relat_1(X2)
        | k1_tarski(X0) != k1_relat_1(X2) )
      & k1_tarski(k4_tarski(X0,X1)) = X2 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ~ ! [X0,X1,X2] :
        ( k1_tarski(k4_tarski(X0,X1)) = X2
       => ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_tarski(X0) = k1_relat_1(X2) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( k1_tarski(k4_tarski(X0,X1)) = X2
         => ( k1_tarski(X1) = k2_relat_1(X2)
            & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( k1_tarski(k4_tarski(X0,X1)) = X2
       => ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relat_1)).

fof(f66,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f32,f63,f59])).

fof(f32,plain,
    ( k1_tarski(sK1) != k2_relat_1(sK2)
    | k1_tarski(sK0) != k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:33:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (23673)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.51  % (23665)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.51  % (23654)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (23652)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (23655)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (23657)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (23671)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (23661)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (23653)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (23663)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (23679)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (23679)Refutation not found, incomplete strategy% (23679)------------------------------
% 0.21/0.53  % (23679)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (23679)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (23679)Memory used [KB]: 1663
% 0.21/0.53  % (23679)Time elapsed: 0.002 s
% 0.21/0.53  % (23679)------------------------------
% 0.21/0.53  % (23679)------------------------------
% 0.21/0.53  % (23651)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (23651)Refutation not found, incomplete strategy% (23651)------------------------------
% 0.21/0.53  % (23651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (23651)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (23651)Memory used [KB]: 1663
% 0.21/0.53  % (23651)Time elapsed: 0.127 s
% 0.21/0.53  % (23651)------------------------------
% 0.21/0.53  % (23651)------------------------------
% 0.21/0.53  % (23674)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.53  % (23662)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  % (23650)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (23667)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (23675)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (23677)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (23676)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (23659)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.54  % (23669)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (23678)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (23668)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (23666)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (23666)Refutation not found, incomplete strategy% (23666)------------------------------
% 0.21/0.55  % (23666)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (23666)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (23666)Memory used [KB]: 10618
% 0.21/0.55  % (23666)Time elapsed: 0.139 s
% 0.21/0.55  % (23666)------------------------------
% 0.21/0.55  % (23666)------------------------------
% 0.21/0.55  % (23658)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.55  % (23660)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (23670)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.56  % (23672)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.56  % (23664)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.56  % (23656)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 2.21/0.67  % (23653)Refutation not found, incomplete strategy% (23653)------------------------------
% 2.21/0.67  % (23653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.67  % (23653)Termination reason: Refutation not found, incomplete strategy
% 2.21/0.67  
% 2.21/0.67  % (23653)Memory used [KB]: 6140
% 2.21/0.67  % (23653)Time elapsed: 0.259 s
% 2.21/0.67  % (23653)------------------------------
% 2.21/0.67  % (23653)------------------------------
% 2.21/0.69  % (23650)Refutation not found, incomplete strategy% (23650)------------------------------
% 2.21/0.69  % (23650)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.69  % (23650)Termination reason: Refutation not found, incomplete strategy
% 2.21/0.69  
% 2.21/0.69  % (23650)Memory used [KB]: 1663
% 2.21/0.69  % (23650)Time elapsed: 0.268 s
% 2.21/0.69  % (23650)------------------------------
% 2.21/0.69  % (23650)------------------------------
% 2.21/0.69  % (23702)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.21/0.70  % (23703)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.21/0.70  % (23701)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 3.07/0.80  % (23652)Time limit reached!
% 3.07/0.80  % (23652)------------------------------
% 3.07/0.80  % (23652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.07/0.80  % (23652)Termination reason: Time limit
% 3.07/0.80  % (23652)Termination phase: Saturation
% 3.07/0.80  
% 3.07/0.80  % (23652)Memory used [KB]: 6780
% 3.07/0.80  % (23652)Time elapsed: 0.400 s
% 3.07/0.80  % (23652)------------------------------
% 3.07/0.80  % (23652)------------------------------
% 3.07/0.81  % (23704)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 3.07/0.82  % (23674)Time limit reached!
% 3.07/0.82  % (23674)------------------------------
% 3.07/0.82  % (23674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.07/0.82  % (23674)Termination reason: Time limit
% 3.07/0.82  % (23674)Termination phase: Saturation
% 3.07/0.82  
% 3.07/0.82  % (23674)Memory used [KB]: 13304
% 3.07/0.82  % (23674)Time elapsed: 0.400 s
% 3.07/0.82  % (23674)------------------------------
% 3.07/0.82  % (23674)------------------------------
% 3.07/0.83  % (23705)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 4.26/0.93  % (23706)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 4.26/0.94  % (23656)Time limit reached!
% 4.26/0.94  % (23656)------------------------------
% 4.26/0.94  % (23656)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.43/0.95  % (23656)Termination reason: Time limit
% 4.43/0.95  % (23656)Termination phase: Saturation
% 4.43/0.95  
% 4.43/0.95  % (23656)Memory used [KB]: 13944
% 4.43/0.95  % (23656)Time elapsed: 0.500 s
% 4.43/0.95  % (23656)------------------------------
% 4.43/0.95  % (23656)------------------------------
% 4.43/0.95  % (23664)Time limit reached!
% 4.43/0.95  % (23664)------------------------------
% 4.43/0.95  % (23664)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.43/0.95  % (23664)Termination reason: Time limit
% 4.43/0.95  
% 4.43/0.95  % (23664)Memory used [KB]: 4989
% 4.43/0.95  % (23664)Time elapsed: 0.530 s
% 4.43/0.95  % (23664)------------------------------
% 4.43/0.95  % (23664)------------------------------
% 4.43/0.97  % (23707)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 4.87/1.06  % (23657)Time limit reached!
% 4.87/1.06  % (23657)------------------------------
% 4.87/1.06  % (23657)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.87/1.06  % (23708)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 5.18/1.07  % (23657)Termination reason: Time limit
% 5.18/1.07  
% 5.18/1.07  % (23657)Memory used [KB]: 9210
% 5.18/1.07  % (23657)Time elapsed: 0.612 s
% 5.18/1.07  % (23657)------------------------------
% 5.18/1.07  % (23657)------------------------------
% 5.18/1.09  % (23709)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 6.20/1.17  % (23710)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 7.78/1.39  % (23703)Time limit reached!
% 7.78/1.39  % (23703)------------------------------
% 7.78/1.39  % (23703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.78/1.39  % (23703)Termination reason: Time limit
% 7.78/1.39  % (23703)Termination phase: Saturation
% 7.78/1.39  
% 7.78/1.39  % (23703)Memory used [KB]: 15223
% 7.78/1.39  % (23703)Time elapsed: 0.800 s
% 7.78/1.39  % (23703)------------------------------
% 7.78/1.39  % (23703)------------------------------
% 7.78/1.41  % (23662)Time limit reached!
% 7.78/1.41  % (23662)------------------------------
% 7.78/1.41  % (23662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.78/1.41  % (23662)Termination reason: Time limit
% 7.78/1.41  % (23662)Termination phase: Saturation
% 7.78/1.41  
% 7.78/1.41  % (23662)Memory used [KB]: 14583
% 7.78/1.41  % (23662)Time elapsed: 1.014 s
% 7.78/1.41  % (23662)------------------------------
% 7.78/1.41  % (23662)------------------------------
% 7.78/1.44  % (23677)Time limit reached!
% 7.78/1.44  % (23677)------------------------------
% 7.78/1.44  % (23677)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.78/1.44  % (23677)Termination reason: Time limit
% 7.78/1.44  
% 7.78/1.44  % (23677)Memory used [KB]: 15095
% 7.78/1.44  % (23677)Time elapsed: 1.011 s
% 7.78/1.44  % (23677)------------------------------
% 7.78/1.44  % (23677)------------------------------
% 8.53/1.45  % (23707)Time limit reached!
% 8.53/1.45  % (23707)------------------------------
% 8.53/1.45  % (23707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.53/1.45  % (23707)Termination reason: Time limit
% 8.53/1.45  
% 8.53/1.45  % (23707)Memory used [KB]: 15479
% 8.53/1.45  % (23707)Time elapsed: 0.605 s
% 8.53/1.45  % (23707)------------------------------
% 8.53/1.45  % (23707)------------------------------
% 8.85/1.54  % (23711)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 9.26/1.57  % (23712)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 9.26/1.57  % (23714)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 9.26/1.57  % (23713)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 10.24/1.74  % (23655)Time limit reached!
% 10.24/1.74  % (23655)------------------------------
% 10.24/1.74  % (23655)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.24/1.74  % (23655)Termination reason: Time limit
% 10.24/1.74  
% 10.24/1.74  % (23655)Memory used [KB]: 9594
% 10.24/1.74  % (23655)Time elapsed: 1.322 s
% 10.24/1.74  % (23655)------------------------------
% 10.24/1.74  % (23655)------------------------------
% 11.65/1.87  % (23715)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 11.65/1.89  % (23714)Time limit reached!
% 11.65/1.89  % (23714)------------------------------
% 11.65/1.89  % (23714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.65/1.89  % (23714)Termination reason: Time limit
% 11.65/1.89  
% 11.65/1.89  % (23714)Memory used [KB]: 15607
% 11.65/1.89  % (23714)Time elapsed: 0.407 s
% 11.65/1.89  % (23714)------------------------------
% 11.65/1.89  % (23714)------------------------------
% 12.40/1.96  % (23710)Time limit reached!
% 12.40/1.96  % (23710)------------------------------
% 12.40/1.96  % (23710)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.40/1.96  % (23710)Termination reason: Time limit
% 12.40/1.96  % (23710)Termination phase: Saturation
% 12.40/1.96  
% 12.40/1.96  % (23710)Memory used [KB]: 22131
% 12.40/1.96  % (23710)Time elapsed: 0.800 s
% 12.40/1.96  % (23710)------------------------------
% 12.40/1.96  % (23710)------------------------------
% 12.82/2.02  % (23716)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 12.82/2.03  % (23676)Time limit reached!
% 12.82/2.03  % (23676)------------------------------
% 12.82/2.03  % (23676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.82/2.03  % (23676)Termination reason: Time limit
% 12.82/2.03  
% 12.82/2.03  % (23676)Memory used [KB]: 23027
% 12.82/2.03  % (23676)Time elapsed: 1.610 s
% 12.82/2.03  % (23676)------------------------------
% 12.82/2.03  % (23676)------------------------------
% 13.29/2.10  % (23717)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 13.56/2.13  % (23716)Refutation not found, incomplete strategy% (23716)------------------------------
% 13.56/2.13  % (23716)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.56/2.13  % (23716)Termination reason: Refutation not found, incomplete strategy
% 13.56/2.13  
% 13.56/2.13  % (23716)Memory used [KB]: 6140
% 13.56/2.13  % (23716)Time elapsed: 0.192 s
% 13.56/2.13  % (23716)------------------------------
% 13.56/2.13  % (23716)------------------------------
% 13.92/2.15  % (23718)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 13.92/2.24  % (23670)Time limit reached!
% 13.92/2.24  % (23670)------------------------------
% 13.92/2.24  % (23670)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.92/2.24  % (23670)Termination reason: Time limit
% 13.92/2.24  
% 13.92/2.24  % (23670)Memory used [KB]: 24306
% 13.92/2.24  % (23670)Time elapsed: 1.815 s
% 13.92/2.24  % (23670)------------------------------
% 13.92/2.24  % (23670)------------------------------
% 14.61/2.25  % (23726)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 15.83/2.39  % (23780)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 16.67/2.50  % (23718)Time limit reached!
% 16.67/2.50  % (23718)------------------------------
% 16.67/2.50  % (23718)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.67/2.50  % (23718)Termination reason: Time limit
% 16.67/2.50  % (23718)Termination phase: Saturation
% 16.67/2.50  
% 16.67/2.50  % (23718)Memory used [KB]: 8571
% 16.67/2.50  % (23718)Time elapsed: 0.400 s
% 16.67/2.50  % (23718)------------------------------
% 16.67/2.50  % (23718)------------------------------
% 17.17/2.53  % (23717)Time limit reached!
% 17.17/2.53  % (23717)------------------------------
% 17.17/2.53  % (23717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.17/2.53  % (23717)Termination reason: Time limit
% 17.17/2.53  
% 17.17/2.53  % (23717)Memory used [KB]: 15351
% 17.17/2.53  % (23717)Time elapsed: 0.511 s
% 17.17/2.53  % (23717)------------------------------
% 17.17/2.53  % (23717)------------------------------
% 17.17/2.62  % (23887)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 17.94/2.67  % (23780)Time limit reached!
% 17.94/2.67  % (23780)------------------------------
% 17.94/2.67  % (23780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.94/2.67  % (23780)Termination reason: Time limit
% 17.94/2.67  % (23780)Termination phase: Saturation
% 17.94/2.67  
% 17.94/2.67  % (23780)Memory used [KB]: 3709
% 17.94/2.67  % (23780)Time elapsed: 0.400 s
% 17.94/2.67  % (23780)------------------------------
% 17.94/2.67  % (23780)------------------------------
% 19.54/2.89  % (23665)Time limit reached!
% 19.54/2.89  % (23665)------------------------------
% 19.54/2.89  % (23665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.54/2.89  % (23665)Termination reason: Time limit
% 19.54/2.89  
% 19.54/2.89  % (23665)Memory used [KB]: 13048
% 19.54/2.89  % (23665)Time elapsed: 2.419 s
% 19.54/2.89  % (23665)------------------------------
% 19.54/2.89  % (23665)------------------------------
% 19.54/2.94  % (23671)Refutation found. Thanks to Tanya!
% 19.54/2.94  % SZS status Theorem for theBenchmark
% 19.54/2.94  % SZS output start Proof for theBenchmark
% 19.54/2.94  % (23887)Time limit reached!
% 19.54/2.94  % (23887)------------------------------
% 19.54/2.94  % (23887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.54/2.94  % (23887)Termination reason: Time limit
% 19.54/2.94  
% 19.54/2.94  % (23887)Memory used [KB]: 7291
% 19.54/2.94  % (23887)Time elapsed: 0.424 s
% 19.54/2.94  % (23887)------------------------------
% 19.54/2.94  % (23887)------------------------------
% 19.54/2.94  fof(f24176,plain,(
% 19.54/2.94    $false),
% 19.54/2.94    inference(avatar_sat_refutation,[],[f66,f71,f101,f1131,f1477,f1555,f13355,f23841,f23974,f24130,f24135,f24173])).
% 19.54/2.94  fof(f24173,plain,(
% 19.54/2.94    spl9_2 | ~spl9_3 | ~spl9_7 | ~spl9_467),
% 19.54/2.94    inference(avatar_contradiction_clause,[],[f24172])).
% 19.54/2.94  fof(f24172,plain,(
% 19.54/2.94    $false | (spl9_2 | ~spl9_3 | ~spl9_7 | ~spl9_467)),
% 19.54/2.94    inference(subsumption_resolution,[],[f24171,f65])).
% 19.54/2.94  fof(f65,plain,(
% 19.54/2.94    k1_tarski(sK1) != k2_relat_1(sK2) | spl9_2),
% 19.54/2.94    inference(avatar_component_clause,[],[f63])).
% 19.54/2.94  fof(f63,plain,(
% 19.54/2.94    spl9_2 <=> k1_tarski(sK1) = k2_relat_1(sK2)),
% 19.54/2.94    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 19.54/2.94  fof(f24171,plain,(
% 19.54/2.94    k1_tarski(sK1) = k2_relat_1(sK2) | (~spl9_3 | ~spl9_7 | ~spl9_467)),
% 19.54/2.94    inference(subsumption_resolution,[],[f24170,f191])).
% 19.54/2.94  fof(f191,plain,(
% 19.54/2.94    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) ) | ~spl9_3),
% 19.54/2.94    inference(resolution,[],[f108,f75])).
% 19.54/2.94  fof(f75,plain,(
% 19.54/2.94    ( ! [X0] : (r2_hidden(k4_tarski(X0,k4_tarski(sK0,sK1)),k2_zfmisc_1(k1_tarski(X0),sK2))) ) | ~spl9_3),
% 19.54/2.94    inference(superposition,[],[f56,f70])).
% 19.54/2.94  fof(f70,plain,(
% 19.54/2.94    sK2 = k1_tarski(k4_tarski(sK0,sK1)) | ~spl9_3),
% 19.54/2.94    inference(avatar_component_clause,[],[f68])).
% 19.54/2.94  fof(f68,plain,(
% 19.54/2.94    spl9_3 <=> sK2 = k1_tarski(k4_tarski(sK0,sK1))),
% 19.54/2.94    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 19.54/2.94  fof(f56,plain,(
% 19.54/2.94    ( ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))) )),
% 19.54/2.94    inference(equality_resolution,[],[f55])).
% 19.54/2.94  fof(f55,plain,(
% 19.54/2.94    ( ! [X2,X0,X3] : (r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) | X0 != X2) )),
% 19.54/2.94    inference(equality_resolution,[],[f43])).
% 19.54/2.94  fof(f43,plain,(
% 19.54/2.94    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) | X1 != X3 | X0 != X2) )),
% 19.54/2.94    inference(cnf_transformation,[],[f28])).
% 19.54/2.94  fof(f28,plain,(
% 19.54/2.94    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) | X1 != X3 | X0 != X2) & ((X1 = X3 & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))))),
% 19.54/2.94    inference(flattening,[],[f27])).
% 19.54/2.94  fof(f27,plain,(
% 19.54/2.94    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) | (X1 != X3 | X0 != X2)) & ((X1 = X3 & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))))),
% 19.54/2.94    inference(nnf_transformation,[],[f5])).
% 19.54/2.94  fof(f5,axiom,(
% 19.54/2.94    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) <=> (X1 = X3 & X0 = X2))),
% 19.54/2.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_zfmisc_1)).
% 19.54/2.94  fof(f108,plain,(
% 19.54/2.94    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,sK2)) | r2_hidden(X0,X2)) ) | ~spl9_3),
% 19.54/2.94    inference(superposition,[],[f44,f70])).
% 19.54/2.94  fof(f44,plain,(
% 19.54/2.94    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | r2_hidden(X0,X2)) )),
% 19.54/2.94    inference(cnf_transformation,[],[f30])).
% 19.54/2.94  fof(f30,plain,(
% 19.54/2.94    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 != X3 | ~r2_hidden(X0,X2)) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 19.54/2.94    inference(flattening,[],[f29])).
% 19.54/2.94  fof(f29,plain,(
% 19.54/2.94    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | (X1 != X3 | ~r2_hidden(X0,X2))) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 19.54/2.94    inference(nnf_transformation,[],[f4])).
% 19.54/2.94  fof(f4,axiom,(
% 19.54/2.94    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 19.54/2.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).
% 19.54/2.94  fof(f24170,plain,(
% 19.54/2.94    ~r2_hidden(sK1,k1_tarski(sK1)) | k1_tarski(sK1) = k2_relat_1(sK2) | (~spl9_7 | ~spl9_467)),
% 19.54/2.94    inference(subsumption_resolution,[],[f24167,f105])).
% 19.54/2.94  fof(f105,plain,(
% 19.54/2.94    r2_hidden(sK1,k2_relat_1(sK2)) | ~spl9_7),
% 19.54/2.94    inference(avatar_component_clause,[],[f103])).
% 19.54/2.94  fof(f103,plain,(
% 19.54/2.94    spl9_7 <=> r2_hidden(sK1,k2_relat_1(sK2))),
% 19.54/2.94    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 19.54/2.94  fof(f24167,plain,(
% 19.54/2.94    ~r2_hidden(sK1,k2_relat_1(sK2)) | ~r2_hidden(sK1,k1_tarski(sK1)) | k1_tarski(sK1) = k2_relat_1(sK2) | ~spl9_467),
% 19.54/2.94    inference(superposition,[],[f152,f23840])).
% 19.54/2.94  fof(f23840,plain,(
% 19.54/2.94    sK1 = sK3(sK2,k1_tarski(sK1)) | ~spl9_467),
% 19.54/2.94    inference(avatar_component_clause,[],[f23838])).
% 19.54/2.94  fof(f23838,plain,(
% 19.54/2.94    spl9_467 <=> sK1 = sK3(sK2,k1_tarski(sK1))),
% 19.54/2.94    introduced(avatar_definition,[new_symbols(naming,[spl9_467])])).
% 19.54/2.94  fof(f152,plain,(
% 19.54/2.94    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),k2_relat_1(X0)) | ~r2_hidden(sK3(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 19.54/2.94    inference(resolution,[],[f36,f52])).
% 19.54/2.94  fof(f52,plain,(
% 19.54/2.94    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 19.54/2.94    inference(equality_resolution,[],[f33])).
% 19.54/2.94  fof(f33,plain,(
% 19.54/2.94    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 19.54/2.94    inference(cnf_transformation,[],[f20])).
% 19.54/2.94  fof(f20,plain,(
% 19.54/2.94    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 19.54/2.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f16,f19,f18,f17])).
% 19.54/2.94  fof(f17,plain,(
% 19.54/2.94    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 19.54/2.94    introduced(choice_axiom,[])).
% 19.54/2.94  fof(f18,plain,(
% 19.54/2.94    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) => r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0))),
% 19.54/2.94    introduced(choice_axiom,[])).
% 19.54/2.94  fof(f19,plain,(
% 19.54/2.94    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0))),
% 19.54/2.94    introduced(choice_axiom,[])).
% 19.54/2.94  fof(f16,plain,(
% 19.54/2.94    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 19.54/2.94    inference(rectify,[],[f15])).
% 19.54/2.94  fof(f15,plain,(
% 19.54/2.94    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 19.54/2.94    inference(nnf_transformation,[],[f8])).
% 19.54/2.94  fof(f8,axiom,(
% 19.54/2.94    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 19.54/2.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 19.54/2.94  fof(f36,plain,(
% 19.54/2.94    ( ! [X0,X3,X1] : (~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | k2_relat_1(X0) = X1 | ~r2_hidden(sK3(X0,X1),X1)) )),
% 19.54/2.94    inference(cnf_transformation,[],[f20])).
% 19.54/2.94  fof(f24135,plain,(
% 19.54/2.94    spl9_467 | ~spl9_3 | ~spl9_465),
% 19.54/2.94    inference(avatar_split_clause,[],[f24133,f23750,f68,f23838])).
% 19.54/2.94  fof(f23750,plain,(
% 19.54/2.94    spl9_465 <=> r2_hidden(sK3(sK2,k1_tarski(sK1)),k1_tarski(sK1))),
% 19.54/2.94    introduced(avatar_definition,[new_symbols(naming,[spl9_465])])).
% 19.54/2.94  fof(f24133,plain,(
% 19.54/2.94    sK1 = sK3(sK2,k1_tarski(sK1)) | (~spl9_3 | ~spl9_465)),
% 19.54/2.94    inference(resolution,[],[f23752,f552])).
% 19.54/2.94  fof(f552,plain,(
% 19.54/2.94    ( ! [X2,X1] : (~r2_hidden(X2,k1_tarski(X1)) | X1 = X2) ) | ~spl9_3),
% 19.54/2.94    inference(resolution,[],[f319,f237])).
% 19.54/2.94  fof(f237,plain,(
% 19.54/2.94    ( ! [X4,X5] : (r2_hidden(X4,k1_relat_1(k2_zfmisc_1(X5,sK2))) | ~r2_hidden(X4,X5)) ) | ~spl9_3),
% 19.54/2.94    inference(resolution,[],[f133,f53])).
% 19.54/2.94  fof(f53,plain,(
% 19.54/2.94    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X5,X6),X0) | r2_hidden(X5,k1_relat_1(X0))) )),
% 19.54/2.94    inference(equality_resolution,[],[f38])).
% 19.54/2.94  fof(f38,plain,(
% 19.54/2.94    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 19.54/2.94    inference(cnf_transformation,[],[f26])).
% 19.54/2.94  fof(f26,plain,(
% 19.54/2.94    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 19.54/2.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f22,f25,f24,f23])).
% 19.54/2.94  fof(f23,plain,(
% 19.54/2.94    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 19.54/2.94    introduced(choice_axiom,[])).
% 19.54/2.94  fof(f24,plain,(
% 19.54/2.94    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0))),
% 19.54/2.94    introduced(choice_axiom,[])).
% 19.54/2.94  fof(f25,plain,(
% 19.54/2.94    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0))),
% 19.54/2.94    introduced(choice_axiom,[])).
% 19.54/2.94  fof(f22,plain,(
% 19.54/2.94    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 19.54/2.94    inference(rectify,[],[f21])).
% 19.54/2.94  fof(f21,plain,(
% 19.54/2.94    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 19.54/2.94    inference(nnf_transformation,[],[f7])).
% 19.54/2.94  fof(f7,axiom,(
% 19.54/2.94    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 19.54/2.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 19.54/2.94  fof(f133,plain,(
% 19.54/2.94    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,k4_tarski(sK0,sK1)),k2_zfmisc_1(X1,sK2)) | ~r2_hidden(X0,X1)) ) | ~spl9_3),
% 19.54/2.94    inference(superposition,[],[f57,f70])).
% 19.54/2.94  fof(f57,plain,(
% 19.54/2.94    ( ! [X2,X0,X3] : (r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(X2,k1_tarski(X3))) | ~r2_hidden(X0,X2)) )),
% 19.54/2.94    inference(equality_resolution,[],[f46])).
% 19.54/2.94  fof(f46,plain,(
% 19.54/2.94    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 != X3 | ~r2_hidden(X0,X2)) )),
% 19.54/2.94    inference(cnf_transformation,[],[f30])).
% 19.54/2.94  fof(f319,plain,(
% 19.54/2.94    ( ! [X4,X3] : (~r2_hidden(X4,k1_relat_1(k2_zfmisc_1(k1_tarski(X3),sK2))) | X3 = X4) ) | ~spl9_3),
% 19.54/2.94    inference(superposition,[],[f150,f78])).
% 19.54/2.94  fof(f78,plain,(
% 19.54/2.94    ( ! [X0] : (k2_zfmisc_1(k1_tarski(X0),sK2) = k1_tarski(k4_tarski(X0,k4_tarski(sK0,sK1)))) ) | ~spl9_3),
% 19.54/2.94    inference(superposition,[],[f47,f70])).
% 19.54/2.94  fof(f47,plain,(
% 19.54/2.94    ( ! [X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))) )),
% 19.54/2.94    inference(cnf_transformation,[],[f6])).
% 19.54/2.94  fof(f6,axiom,(
% 19.54/2.94    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))),
% 19.54/2.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).
% 19.54/2.94  fof(f150,plain,(
% 19.54/2.94    ( ! [X6,X4,X5] : (~r2_hidden(X4,k1_relat_1(k1_tarski(k4_tarski(X5,X6)))) | X4 = X5) )),
% 19.54/2.94    inference(resolution,[],[f135,f54])).
% 19.54/2.94  fof(f54,plain,(
% 19.54/2.94    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 19.54/2.94    inference(equality_resolution,[],[f37])).
% 19.54/2.94  fof(f37,plain,(
% 19.54/2.94    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 19.54/2.94    inference(cnf_transformation,[],[f26])).
% 19.54/2.94  fof(f135,plain,(
% 19.54/2.94    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k1_tarski(k4_tarski(X2,X3))) | X0 = X2) )),
% 19.54/2.94    inference(forward_demodulation,[],[f41,f47])).
% 19.54/2.94  fof(f41,plain,(
% 19.54/2.94    ( ! [X2,X0,X3,X1] : (X0 = X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))) )),
% 19.54/2.94    inference(cnf_transformation,[],[f28])).
% 19.54/2.94  fof(f23752,plain,(
% 19.54/2.94    r2_hidden(sK3(sK2,k1_tarski(sK1)),k1_tarski(sK1)) | ~spl9_465),
% 19.54/2.94    inference(avatar_component_clause,[],[f23750])).
% 19.54/2.94  fof(f24130,plain,(
% 19.54/2.94    spl9_465 | spl9_2 | spl9_468),
% 19.54/2.94    inference(avatar_split_clause,[],[f24129,f23844,f63,f23750])).
% 19.54/2.94  fof(f23844,plain,(
% 19.54/2.94    spl9_468 <=> r2_hidden(sK3(sK2,k1_tarski(sK1)),k2_relat_1(sK2))),
% 19.54/2.94    introduced(avatar_definition,[new_symbols(naming,[spl9_468])])).
% 19.54/2.94  fof(f24129,plain,(
% 19.54/2.94    r2_hidden(sK3(sK2,k1_tarski(sK1)),k1_tarski(sK1)) | (spl9_2 | spl9_468)),
% 19.54/2.94    inference(subsumption_resolution,[],[f24127,f65])).
% 19.54/2.94  fof(f24127,plain,(
% 19.54/2.94    r2_hidden(sK3(sK2,k1_tarski(sK1)),k1_tarski(sK1)) | k1_tarski(sK1) = k2_relat_1(sK2) | spl9_468),
% 19.54/2.94    inference(resolution,[],[f23845,f160])).
% 19.54/2.94  fof(f160,plain,(
% 19.54/2.94    ( ! [X4,X5] : (r2_hidden(sK3(X4,X5),k2_relat_1(X4)) | r2_hidden(sK3(X4,X5),X5) | k2_relat_1(X4) = X5) )),
% 19.54/2.94    inference(resolution,[],[f35,f51])).
% 19.54/2.94  fof(f51,plain,(
% 19.54/2.94    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X6,X5),X0) | r2_hidden(X5,k2_relat_1(X0))) )),
% 19.54/2.94    inference(equality_resolution,[],[f34])).
% 19.54/2.94  fof(f34,plain,(
% 19.54/2.94    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 19.54/2.94    inference(cnf_transformation,[],[f20])).
% 19.54/2.94  fof(f35,plain,(
% 19.54/2.94    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | k2_relat_1(X0) = X1 | r2_hidden(sK3(X0,X1),X1)) )),
% 19.54/2.94    inference(cnf_transformation,[],[f20])).
% 19.54/2.94  fof(f23845,plain,(
% 19.54/2.94    ~r2_hidden(sK3(sK2,k1_tarski(sK1)),k2_relat_1(sK2)) | spl9_468),
% 19.54/2.94    inference(avatar_component_clause,[],[f23844])).
% 19.54/2.94  fof(f23974,plain,(
% 19.54/2.94    ~spl9_468 | ~spl9_3 | spl9_466),
% 19.54/2.94    inference(avatar_split_clause,[],[f23970,f23754,f68,f23844])).
% 19.54/2.94  fof(f23754,plain,(
% 19.54/2.94    spl9_466 <=> r2_hidden(k4_tarski(sK0,sK3(sK2,k1_tarski(sK1))),sK2)),
% 19.54/2.94    introduced(avatar_definition,[new_symbols(naming,[spl9_466])])).
% 19.54/2.94  fof(f23970,plain,(
% 19.54/2.94    ~r2_hidden(sK3(sK2,k1_tarski(sK1)),k2_relat_1(sK2)) | (~spl9_3 | spl9_466)),
% 19.54/2.94    inference(resolution,[],[f23755,f309])).
% 19.54/2.94  fof(f309,plain,(
% 19.54/2.94    ( ! [X1] : (r2_hidden(k4_tarski(sK0,X1),sK2) | ~r2_hidden(X1,k2_relat_1(sK2))) ) | ~spl9_3),
% 19.54/2.94    inference(duplicate_literal_removal,[],[f308])).
% 19.54/2.94  fof(f308,plain,(
% 19.54/2.94    ( ! [X1] : (r2_hidden(k4_tarski(sK0,X1),sK2) | ~r2_hidden(X1,k2_relat_1(sK2)) | ~r2_hidden(X1,k2_relat_1(sK2))) ) | ~spl9_3),
% 19.54/2.94    inference(superposition,[],[f52,f156])).
% 19.54/2.94  fof(f156,plain,(
% 19.54/2.94    ( ! [X0] : (sK0 = sK5(sK2,X0) | ~r2_hidden(X0,k2_relat_1(sK2))) ) | ~spl9_3),
% 19.54/2.94    inference(resolution,[],[f151,f52])).
% 19.54/2.94  fof(f151,plain,(
% 19.54/2.94    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | sK0 = X0) ) | ~spl9_3),
% 19.54/2.94    inference(superposition,[],[f135,f70])).
% 19.54/2.94  fof(f23755,plain,(
% 19.54/2.94    ~r2_hidden(k4_tarski(sK0,sK3(sK2,k1_tarski(sK1))),sK2) | spl9_466),
% 19.54/2.94    inference(avatar_component_clause,[],[f23754])).
% 19.54/2.94  fof(f23841,plain,(
% 19.54/2.94    spl9_467 | ~spl9_3 | ~spl9_466),
% 19.54/2.94    inference(avatar_split_clause,[],[f23824,f23754,f68,f23838])).
% 19.54/2.94  fof(f23824,plain,(
% 19.54/2.94    sK1 = sK3(sK2,k1_tarski(sK1)) | (~spl9_3 | ~spl9_466)),
% 19.54/2.94    inference(resolution,[],[f23756,f325])).
% 19.54/2.94  fof(f325,plain,(
% 19.54/2.94    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | sK1 = X1) ) | ~spl9_3),
% 19.54/2.94    inference(superposition,[],[f112,f70])).
% 19.54/2.94  fof(f112,plain,(
% 19.54/2.94    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),k1_tarski(k4_tarski(X0,X1))) | X1 = X3) )),
% 19.54/2.94    inference(superposition,[],[f45,f47])).
% 19.54/2.94  fof(f45,plain,(
% 19.54/2.94    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 = X3) )),
% 19.54/2.94    inference(cnf_transformation,[],[f30])).
% 19.54/2.94  fof(f23756,plain,(
% 19.54/2.94    r2_hidden(k4_tarski(sK0,sK3(sK2,k1_tarski(sK1))),sK2) | ~spl9_466),
% 19.54/2.94    inference(avatar_component_clause,[],[f23754])).
% 19.54/2.94  fof(f13355,plain,(
% 19.54/2.94    spl9_5 | ~spl9_3),
% 19.54/2.94    inference(avatar_split_clause,[],[f13269,f68,f91])).
% 20.46/2.94  fof(f91,plain,(
% 20.46/2.94    spl9_5 <=> r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 20.46/2.94    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 20.46/2.94  fof(f13269,plain,(
% 20.46/2.94    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~spl9_3),
% 20.46/2.94    inference(superposition,[],[f191,f70])).
% 20.46/2.94  fof(f1555,plain,(
% 20.46/2.94    spl9_7 | ~spl9_3),
% 20.46/2.94    inference(avatar_split_clause,[],[f1520,f68,f103])).
% 20.46/2.94  fof(f1520,plain,(
% 20.46/2.94    r2_hidden(sK1,k2_relat_1(sK2)) | ~spl9_3),
% 20.46/2.94    inference(superposition,[],[f209,f70])).
% 20.46/2.94  fof(f209,plain,(
% 20.46/2.94    ( ! [X4,X3] : (r2_hidden(X3,k2_relat_1(k1_tarski(k4_tarski(X4,X3))))) ) | ~spl9_3),
% 20.46/2.94    inference(resolution,[],[f191,f51])).
% 20.46/2.94  fof(f1477,plain,(
% 20.46/2.94    spl9_1 | ~spl9_3 | ~spl9_6 | ~spl9_35),
% 20.46/2.94    inference(avatar_split_clause,[],[f1467,f1117,f98,f68,f59])).
% 20.46/2.94  fof(f59,plain,(
% 20.46/2.94    spl9_1 <=> k1_tarski(sK0) = k1_relat_1(sK2)),
% 20.46/2.94    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 20.46/2.94  fof(f98,plain,(
% 20.46/2.94    spl9_6 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 20.46/2.94    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 20.46/2.94  fof(f1117,plain,(
% 20.46/2.94    spl9_35 <=> sK0 = sK6(sK2,k1_tarski(sK0))),
% 20.46/2.94    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).
% 20.46/2.94  fof(f1467,plain,(
% 20.46/2.94    k1_tarski(sK0) = k1_relat_1(sK2) | (~spl9_3 | ~spl9_6 | ~spl9_35)),
% 20.46/2.94    inference(subsumption_resolution,[],[f1466,f191])).
% 20.46/2.94  fof(f1466,plain,(
% 20.46/2.94    ~r2_hidden(sK0,k1_tarski(sK0)) | k1_tarski(sK0) = k1_relat_1(sK2) | (~spl9_6 | ~spl9_35)),
% 20.46/2.94    inference(subsumption_resolution,[],[f1463,f100])).
% 20.46/2.94  fof(f100,plain,(
% 20.46/2.94    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl9_6),
% 20.46/2.94    inference(avatar_component_clause,[],[f98])).
% 20.46/2.94  fof(f1463,plain,(
% 20.46/2.94    ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(sK0,k1_tarski(sK0)) | k1_tarski(sK0) = k1_relat_1(sK2) | ~spl9_35),
% 20.46/2.94    inference(superposition,[],[f153,f1119])).
% 20.46/2.94  fof(f1119,plain,(
% 20.46/2.94    sK0 = sK6(sK2,k1_tarski(sK0)) | ~spl9_35),
% 20.46/2.94    inference(avatar_component_clause,[],[f1117])).
% 20.46/2.94  fof(f153,plain,(
% 20.46/2.94    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),k1_relat_1(X0)) | ~r2_hidden(sK6(X0,X1),X1) | k1_relat_1(X0) = X1) )),
% 20.46/2.94    inference(resolution,[],[f40,f54])).
% 20.46/2.94  fof(f40,plain,(
% 20.46/2.94    ( ! [X0,X3,X1] : (~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | k1_relat_1(X0) = X1 | ~r2_hidden(sK6(X0,X1),X1)) )),
% 20.46/2.94    inference(cnf_transformation,[],[f26])).
% 20.46/2.94  fof(f1131,plain,(
% 20.46/2.94    spl9_35 | spl9_1 | ~spl9_3),
% 20.46/2.94    inference(avatar_split_clause,[],[f1130,f68,f59,f1117])).
% 20.46/2.94  fof(f1130,plain,(
% 20.46/2.94    k1_tarski(sK0) = k1_relat_1(sK2) | sK0 = sK6(sK2,k1_tarski(sK0)) | ~spl9_3),
% 20.46/2.94    inference(subsumption_resolution,[],[f1099,f157])).
% 20.46/2.94  fof(f157,plain,(
% 20.46/2.94    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK2)) | sK0 = X1) ) | ~spl9_3),
% 20.46/2.94    inference(resolution,[],[f151,f54])).
% 20.46/2.94  fof(f1099,plain,(
% 20.46/2.94    k1_tarski(sK0) = k1_relat_1(sK2) | sK0 = sK6(sK2,k1_tarski(sK0)) | r2_hidden(sK6(sK2,k1_tarski(sK0)),k1_relat_1(sK2)) | ~spl9_3),
% 20.46/2.94    inference(resolution,[],[f172,f499])).
% 20.46/2.94  fof(f499,plain,(
% 20.46/2.94    ( ! [X3] : (~r2_hidden(X3,k1_tarski(sK0)) | r2_hidden(X3,k1_relat_1(sK2))) ) | ~spl9_3),
% 20.46/2.94    inference(resolution,[],[f354,f53])).
% 20.46/2.94  fof(f354,plain,(
% 20.46/2.94    ( ! [X0] : (r2_hidden(k4_tarski(X0,sK1),sK2) | ~r2_hidden(X0,k1_tarski(sK0))) ) | ~spl9_3),
% 20.46/2.94    inference(superposition,[],[f134,f70])).
% 20.46/2.94  fof(f134,plain,(
% 20.46/2.94    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,X1),k1_tarski(k4_tarski(X0,X1))) | ~r2_hidden(X2,k1_tarski(X0))) )),
% 20.46/2.94    inference(superposition,[],[f57,f47])).
% 20.46/2.94  fof(f172,plain,(
% 20.46/2.94    ( ! [X15] : (r2_hidden(sK6(sK2,X15),X15) | k1_relat_1(sK2) = X15 | sK0 = sK6(sK2,X15)) ) | ~spl9_3),
% 20.46/2.94    inference(resolution,[],[f39,f151])).
% 20.46/2.94  fof(f39,plain,(
% 20.46/2.94    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) | k1_relat_1(X0) = X1 | r2_hidden(sK6(X0,X1),X1)) )),
% 20.46/2.94    inference(cnf_transformation,[],[f26])).
% 20.46/2.94  fof(f101,plain,(
% 20.46/2.94    spl9_6 | ~spl9_5),
% 20.46/2.94    inference(avatar_split_clause,[],[f95,f91,f98])).
% 20.46/2.94  fof(f95,plain,(
% 20.46/2.94    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl9_5),
% 20.46/2.94    inference(resolution,[],[f93,f53])).
% 20.46/2.94  fof(f93,plain,(
% 20.46/2.94    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~spl9_5),
% 20.46/2.94    inference(avatar_component_clause,[],[f91])).
% 20.46/2.94  fof(f71,plain,(
% 20.46/2.94    spl9_3),
% 20.46/2.94    inference(avatar_split_clause,[],[f31,f68])).
% 20.46/2.94  fof(f31,plain,(
% 20.46/2.94    sK2 = k1_tarski(k4_tarski(sK0,sK1))),
% 20.46/2.94    inference(cnf_transformation,[],[f14])).
% 20.46/2.94  fof(f14,plain,(
% 20.46/2.94    (k1_tarski(sK1) != k2_relat_1(sK2) | k1_tarski(sK0) != k1_relat_1(sK2)) & sK2 = k1_tarski(k4_tarski(sK0,sK1))),
% 20.46/2.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).
% 20.46/2.94  fof(f13,plain,(
% 20.46/2.94    ? [X0,X1,X2] : ((k1_tarski(X1) != k2_relat_1(X2) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2) => ((k1_tarski(sK1) != k2_relat_1(sK2) | k1_tarski(sK0) != k1_relat_1(sK2)) & sK2 = k1_tarski(k4_tarski(sK0,sK1)))),
% 20.46/2.94    introduced(choice_axiom,[])).
% 20.46/2.94  fof(f12,plain,(
% 20.46/2.94    ? [X0,X1,X2] : ((k1_tarski(X1) != k2_relat_1(X2) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2)),
% 20.46/2.94    inference(ennf_transformation,[],[f11])).
% 20.46/2.94  fof(f11,plain,(
% 20.46/2.94    ~! [X0,X1,X2] : (k1_tarski(k4_tarski(X0,X1)) = X2 => (k1_tarski(X1) = k2_relat_1(X2) & k1_tarski(X0) = k1_relat_1(X2)))),
% 20.46/2.94    inference(pure_predicate_removal,[],[f10])).
% 20.46/2.94  fof(f10,negated_conjecture,(
% 20.46/2.94    ~! [X0,X1,X2] : (v1_relat_1(X2) => (k1_tarski(k4_tarski(X0,X1)) = X2 => (k1_tarski(X1) = k2_relat_1(X2) & k1_tarski(X0) = k1_relat_1(X2))))),
% 20.46/2.94    inference(negated_conjecture,[],[f9])).
% 20.46/2.94  fof(f9,conjecture,(
% 20.46/2.94    ! [X0,X1,X2] : (v1_relat_1(X2) => (k1_tarski(k4_tarski(X0,X1)) = X2 => (k1_tarski(X1) = k2_relat_1(X2) & k1_tarski(X0) = k1_relat_1(X2))))),
% 20.46/2.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relat_1)).
% 20.46/2.94  fof(f66,plain,(
% 20.46/2.94    ~spl9_1 | ~spl9_2),
% 20.46/2.94    inference(avatar_split_clause,[],[f32,f63,f59])).
% 20.46/2.94  fof(f32,plain,(
% 20.46/2.94    k1_tarski(sK1) != k2_relat_1(sK2) | k1_tarski(sK0) != k1_relat_1(sK2)),
% 20.46/2.94    inference(cnf_transformation,[],[f14])).
% 20.46/2.94  % SZS output end Proof for theBenchmark
% 20.46/2.94  % (23671)------------------------------
% 20.46/2.94  % (23671)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.46/2.94  % (23671)Termination reason: Refutation
% 20.46/2.94  
% 20.46/2.94  % (23671)Memory used [KB]: 23922
% 20.46/2.94  % (23671)Time elapsed: 2.501 s
% 20.46/2.94  % (23671)------------------------------
% 20.46/2.94  % (23671)------------------------------
% 20.46/2.94  % (23649)Success in time 2.59 s
%------------------------------------------------------------------------------
