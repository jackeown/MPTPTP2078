%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 199 expanded)
%              Number of leaves         :   17 (  77 expanded)
%              Depth                    :   10
%              Number of atoms          :  224 ( 399 expanded)
%              Number of equality atoms :   95 ( 215 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f760,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f85,f92,f97,f106,f159,f350,f444,f570,f759])).

fof(f759,plain,
    ( ~ spl10_4
    | spl10_7
    | ~ spl10_22 ),
    inference(avatar_split_clause,[],[f757,f441,f103,f89])).

fof(f89,plain,
    ( spl10_4
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f103,plain,
    ( spl10_7
  <=> k1_relat_1(sK2) = k1_enumset1(sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f441,plain,
    ( spl10_22
  <=> sK0 = sK9(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f757,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | spl10_7
    | ~ spl10_22 ),
    inference(trivial_inequality_removal,[],[f756])).

fof(f756,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | k1_relat_1(sK2) != k1_relat_1(sK2)
    | sK0 != sK0
    | spl10_7
    | ~ spl10_22 ),
    inference(superposition,[],[f479,f443])).

fof(f443,plain,
    ( sK0 = sK9(sK0,k1_relat_1(sK2))
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f441])).

fof(f479,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK9(sK0,X1),X1)
        | k1_relat_1(sK2) != X1
        | sK0 != sK9(sK0,X1) )
    | spl10_7 ),
    inference(superposition,[],[f105,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X0,X0,X0) = X1
      | ~ r2_hidden(sK9(X0,X1),X1)
      | sK9(X0,X1) != X0 ) ),
    inference(definition_unfolding,[],[f28,f34])).

fof(f34,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f15,f16])).

fof(f16,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f15,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( sK9(X0,X1) != X0
      | ~ r2_hidden(sK9(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f105,plain,
    ( k1_relat_1(sK2) != k1_enumset1(sK0,sK0,sK0)
    | spl10_7 ),
    inference(avatar_component_clause,[],[f103])).

fof(f570,plain,
    ( ~ spl10_5
    | spl10_6
    | ~ spl10_17 ),
    inference(avatar_split_clause,[],[f568,f347,f99,f94])).

fof(f94,plain,
    ( spl10_5
  <=> r2_hidden(sK1,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f99,plain,
    ( spl10_6
  <=> k2_relat_1(sK2) = k1_enumset1(sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f347,plain,
    ( spl10_17
  <=> sK1 = sK9(sK1,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f568,plain,
    ( ~ r2_hidden(sK1,k2_relat_1(sK2))
    | spl10_6
    | ~ spl10_17 ),
    inference(trivial_inequality_removal,[],[f567])).

fof(f567,plain,
    ( ~ r2_hidden(sK1,k2_relat_1(sK2))
    | k2_relat_1(sK2) != k2_relat_1(sK2)
    | sK1 != sK1
    | spl10_6
    | ~ spl10_17 ),
    inference(superposition,[],[f385,f349])).

% (6951)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
fof(f349,plain,
    ( sK1 = sK9(sK1,k2_relat_1(sK2))
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f347])).

fof(f385,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK9(sK1,X1),X1)
        | k2_relat_1(sK2) != X1
        | sK1 != sK9(sK1,X1) )
    | spl10_6 ),
    inference(superposition,[],[f101,f37])).

fof(f101,plain,
    ( k2_relat_1(sK2) != k1_enumset1(sK1,sK1,sK1)
    | spl10_6 ),
    inference(avatar_component_clause,[],[f99])).

fof(f444,plain,
    ( spl10_22
    | spl10_7
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f439,f153,f103,f441])).

fof(f153,plain,
    ( spl10_10
  <=> sK2 = k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f439,plain,
    ( sK0 = sK9(sK0,k1_relat_1(sK2))
    | spl10_7
    | ~ spl10_10 ),
    inference(trivial_inequality_removal,[],[f438])).

fof(f438,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | sK0 = sK9(sK0,k1_relat_1(sK2))
    | spl10_7
    | ~ spl10_10 ),
    inference(duplicate_literal_removal,[],[f435])).

fof(f435,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | sK0 = sK9(sK0,k1_relat_1(sK2))
    | sK0 = sK9(sK0,k1_relat_1(sK2))
    | spl10_7
    | ~ spl10_10 ),
    inference(resolution,[],[f376,f173])).

fof(f173,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relat_1(sK2))
        | sK0 = X3 )
    | ~ spl10_10 ),
    inference(resolution,[],[f166,f48])).

fof(f48,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK7(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK7(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f166,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | sK0 = X0 )
    | ~ spl10_10 ),
    inference(superposition,[],[f45,f155])).

fof(f155,plain,
    ( sK2 = k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f153])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_enumset1(X2,X2,X2),k1_enumset1(X3,X3,X3)))
      | X0 = X2 ) ),
    inference(definition_unfolding,[],[f31,f34,f34])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
    <=> ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_zfmisc_1)).

fof(f376,plain,
    ( ! [X0] :
        ( r2_hidden(sK9(sK0,X0),X0)
        | k1_relat_1(sK2) != X0
        | sK0 = sK9(sK0,X0) )
    | spl10_7 ),
    inference(superposition,[],[f105,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X0,X0,X0) = X1
      | r2_hidden(sK9(X0,X1),X1)
      | sK9(X0,X1) = X0 ) ),
    inference(definition_unfolding,[],[f27,f34])).

fof(f27,plain,(
    ! [X0,X1] :
      ( sK9(X0,X1) = X0
      | r2_hidden(sK9(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f350,plain,
    ( spl10_17
    | spl10_6
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f345,f153,f99,f347])).

fof(f345,plain,
    ( sK1 = sK9(sK1,k2_relat_1(sK2))
    | spl10_6
    | ~ spl10_10 ),
    inference(trivial_inequality_removal,[],[f344])).

fof(f344,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | sK1 = sK9(sK1,k2_relat_1(sK2))
    | spl10_6
    | ~ spl10_10 ),
    inference(duplicate_literal_removal,[],[f342])).

fof(f342,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | sK1 = sK9(sK1,k2_relat_1(sK2))
    | sK1 = sK9(sK1,k2_relat_1(sK2))
    | spl10_6
    | ~ spl10_10 ),
    inference(resolution,[],[f107,f193])).

fof(f193,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_relat_1(sK2))
        | sK1 = X1 )
    | ~ spl10_10 ),
    inference(resolution,[],[f167,f46])).

fof(f46,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK4(X0,X2),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f18])).

% (6962)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
fof(f18,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f167,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK2)
        | sK1 = X3 )
    | ~ spl10_10 ),
    inference(superposition,[],[f44,f155])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_enumset1(X2,X2,X2),k1_enumset1(X3,X3,X3)))
      | X1 = X3 ) ),
    inference(definition_unfolding,[],[f32,f34,f34])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f107,plain,
    ( ! [X0] :
        ( r2_hidden(sK9(sK1,X0),X0)
        | k2_relat_1(sK2) != X0
        | sK1 = sK9(sK1,X0) )
    | spl10_6 ),
    inference(superposition,[],[f101,f38])).

fof(f159,plain,
    ( spl10_10
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f70,f61,f153])).

fof(f61,plain,
    ( spl10_2
  <=> sK2 = k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f70,plain,
    ( sK2 = k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))
    | ~ spl10_2 ),
    inference(superposition,[],[f42,f63])).

fof(f63,plain,
    ( sK2 = k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f42,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)) = k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(definition_unfolding,[],[f29,f34,f16,f16])).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f106,plain,
    ( ~ spl10_6
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f36,f103,f99])).

fof(f36,plain,
    ( k1_relat_1(sK2) != k1_enumset1(sK0,sK0,sK0)
    | k2_relat_1(sK2) != k1_enumset1(sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f12,f34,f34])).

fof(f12,plain,
    ( k1_tarski(sK0) != k1_relat_1(sK2)
    | k2_relat_1(sK2) != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relat_1(X2) != k1_tarski(X1)
        | k1_tarski(X0) != k1_relat_1(X2) )
      & k1_tarski(k4_tarski(X0,X1)) = X2
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relat_1(X2) != k1_tarski(X1)
        | k1_tarski(X0) != k1_relat_1(X2) )
      & k1_tarski(k4_tarski(X0,X1)) = X2
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( k1_tarski(k4_tarski(X0,X1)) = X2
         => ( k2_relat_1(X2) = k1_tarski(X1)
            & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( k1_tarski(k4_tarski(X0,X1)) = X2
       => ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relat_1)).

fof(f97,plain,
    ( spl10_5
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f87,f82,f94])).

fof(f82,plain,
    ( spl10_3
  <=> r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f87,plain,
    ( r2_hidden(sK1,k2_relat_1(sK2))
    | ~ spl10_3 ),
    inference(resolution,[],[f84,f47])).

fof(f47,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f84,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f92,plain,
    ( spl10_4
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f86,f82,f89])).

fof(f86,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl10_3 ),
    inference(resolution,[],[f84,f49])).

fof(f49,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f85,plain,
    ( spl10_3
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f78,f61,f82])).

fof(f78,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl10_2 ),
    inference(superposition,[],[f52,f63])).

fof(f52,plain,(
    ! [X2] : r2_hidden(X2,k1_enumset1(X2,X2,X2)) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_enumset1(X2,X2,X2) != X1 ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f25,f34])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f64,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f35,f61])).

fof(f35,plain,(
    sK2 = k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) ),
    inference(definition_unfolding,[],[f14,f34])).

fof(f14,plain,(
    sK2 = k1_tarski(k4_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:38:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (6965)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.50  % (6949)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.51  % (6941)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (6938)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (6946)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.52  % (6942)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (6937)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (6947)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (6943)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (6940)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.53  % (6964)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.53  % (6948)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.54  % (6956)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.54  % (6955)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.54  % (6952)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (6963)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (6965)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f760,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(avatar_sat_refutation,[],[f64,f85,f92,f97,f106,f159,f350,f444,f570,f759])).
% 0.22/0.55  fof(f759,plain,(
% 0.22/0.55    ~spl10_4 | spl10_7 | ~spl10_22),
% 0.22/0.55    inference(avatar_split_clause,[],[f757,f441,f103,f89])).
% 0.22/0.55  fof(f89,plain,(
% 0.22/0.55    spl10_4 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.22/0.55  fof(f103,plain,(
% 0.22/0.55    spl10_7 <=> k1_relat_1(sK2) = k1_enumset1(sK0,sK0,sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.22/0.55  fof(f441,plain,(
% 0.22/0.55    spl10_22 <=> sK0 = sK9(sK0,k1_relat_1(sK2))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).
% 0.22/0.55  fof(f757,plain,(
% 0.22/0.55    ~r2_hidden(sK0,k1_relat_1(sK2)) | (spl10_7 | ~spl10_22)),
% 0.22/0.55    inference(trivial_inequality_removal,[],[f756])).
% 0.22/0.55  fof(f756,plain,(
% 0.22/0.55    ~r2_hidden(sK0,k1_relat_1(sK2)) | k1_relat_1(sK2) != k1_relat_1(sK2) | sK0 != sK0 | (spl10_7 | ~spl10_22)),
% 0.22/0.55    inference(superposition,[],[f479,f443])).
% 0.22/0.55  fof(f443,plain,(
% 0.22/0.55    sK0 = sK9(sK0,k1_relat_1(sK2)) | ~spl10_22),
% 0.22/0.55    inference(avatar_component_clause,[],[f441])).
% 0.22/0.55  fof(f479,plain,(
% 0.22/0.55    ( ! [X1] : (~r2_hidden(sK9(sK0,X1),X1) | k1_relat_1(sK2) != X1 | sK0 != sK9(sK0,X1)) ) | spl10_7),
% 0.22/0.55    inference(superposition,[],[f105,f37])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X0) = X1 | ~r2_hidden(sK9(X0,X1),X1) | sK9(X0,X1) != X0) )),
% 0.22/0.55    inference(definition_unfolding,[],[f28,f34])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f15,f16])).
% 0.22/0.55  fof(f16,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.55  fof(f15,plain,(
% 0.22/0.55    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ( ! [X0,X1] : (sK9(X0,X1) != X0 | ~r2_hidden(sK9(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.22/0.55  fof(f105,plain,(
% 0.22/0.55    k1_relat_1(sK2) != k1_enumset1(sK0,sK0,sK0) | spl10_7),
% 0.22/0.55    inference(avatar_component_clause,[],[f103])).
% 0.22/0.55  fof(f570,plain,(
% 0.22/0.55    ~spl10_5 | spl10_6 | ~spl10_17),
% 0.22/0.55    inference(avatar_split_clause,[],[f568,f347,f99,f94])).
% 0.22/0.55  fof(f94,plain,(
% 0.22/0.55    spl10_5 <=> r2_hidden(sK1,k2_relat_1(sK2))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.22/0.55  fof(f99,plain,(
% 0.22/0.55    spl10_6 <=> k2_relat_1(sK2) = k1_enumset1(sK1,sK1,sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.22/0.55  fof(f347,plain,(
% 0.22/0.55    spl10_17 <=> sK1 = sK9(sK1,k2_relat_1(sK2))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 0.22/0.55  fof(f568,plain,(
% 0.22/0.55    ~r2_hidden(sK1,k2_relat_1(sK2)) | (spl10_6 | ~spl10_17)),
% 0.22/0.55    inference(trivial_inequality_removal,[],[f567])).
% 0.22/0.55  fof(f567,plain,(
% 0.22/0.55    ~r2_hidden(sK1,k2_relat_1(sK2)) | k2_relat_1(sK2) != k2_relat_1(sK2) | sK1 != sK1 | (spl10_6 | ~spl10_17)),
% 0.22/0.55    inference(superposition,[],[f385,f349])).
% 0.22/0.55  % (6951)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.55  fof(f349,plain,(
% 0.22/0.55    sK1 = sK9(sK1,k2_relat_1(sK2)) | ~spl10_17),
% 0.22/0.55    inference(avatar_component_clause,[],[f347])).
% 0.22/0.55  fof(f385,plain,(
% 0.22/0.55    ( ! [X1] : (~r2_hidden(sK9(sK1,X1),X1) | k2_relat_1(sK2) != X1 | sK1 != sK9(sK1,X1)) ) | spl10_6),
% 0.22/0.55    inference(superposition,[],[f101,f37])).
% 0.22/0.55  fof(f101,plain,(
% 0.22/0.55    k2_relat_1(sK2) != k1_enumset1(sK1,sK1,sK1) | spl10_6),
% 0.22/0.55    inference(avatar_component_clause,[],[f99])).
% 0.22/0.55  fof(f444,plain,(
% 0.22/0.55    spl10_22 | spl10_7 | ~spl10_10),
% 0.22/0.55    inference(avatar_split_clause,[],[f439,f153,f103,f441])).
% 0.22/0.55  fof(f153,plain,(
% 0.22/0.55    spl10_10 <=> sK2 = k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 0.22/0.55  fof(f439,plain,(
% 0.22/0.55    sK0 = sK9(sK0,k1_relat_1(sK2)) | (spl10_7 | ~spl10_10)),
% 0.22/0.55    inference(trivial_inequality_removal,[],[f438])).
% 0.22/0.55  fof(f438,plain,(
% 0.22/0.55    k1_relat_1(sK2) != k1_relat_1(sK2) | sK0 = sK9(sK0,k1_relat_1(sK2)) | (spl10_7 | ~spl10_10)),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f435])).
% 0.22/0.55  fof(f435,plain,(
% 0.22/0.55    k1_relat_1(sK2) != k1_relat_1(sK2) | sK0 = sK9(sK0,k1_relat_1(sK2)) | sK0 = sK9(sK0,k1_relat_1(sK2)) | (spl10_7 | ~spl10_10)),
% 0.22/0.55    inference(resolution,[],[f376,f173])).
% 0.22/0.55  fof(f173,plain,(
% 0.22/0.55    ( ! [X3] : (~r2_hidden(X3,k1_relat_1(sK2)) | sK0 = X3) ) | ~spl10_10),
% 0.22/0.55    inference(resolution,[],[f166,f48])).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,sK7(X0,X2)),X0) | ~r2_hidden(X2,k1_relat_1(X0))) )),
% 0.22/0.55    inference(equality_resolution,[],[f22])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK7(X0,X2)),X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.22/0.55  fof(f166,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | sK0 = X0) ) | ~spl10_10),
% 0.22/0.55    inference(superposition,[],[f45,f155])).
% 0.22/0.55  fof(f155,plain,(
% 0.22/0.55    sK2 = k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)) | ~spl10_10),
% 0.22/0.55    inference(avatar_component_clause,[],[f153])).
% 0.22/0.55  fof(f45,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_enumset1(X2,X2,X2),k1_enumset1(X3,X3,X3))) | X0 = X2) )),
% 0.22/0.55    inference(definition_unfolding,[],[f31,f34,f34])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (X0 = X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) <=> (X1 = X3 & X0 = X2))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_zfmisc_1)).
% 0.22/0.55  fof(f376,plain,(
% 0.22/0.55    ( ! [X0] : (r2_hidden(sK9(sK0,X0),X0) | k1_relat_1(sK2) != X0 | sK0 = sK9(sK0,X0)) ) | spl10_7),
% 0.22/0.55    inference(superposition,[],[f105,f38])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X0) = X1 | r2_hidden(sK9(X0,X1),X1) | sK9(X0,X1) = X0) )),
% 0.22/0.55    inference(definition_unfolding,[],[f27,f34])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ( ! [X0,X1] : (sK9(X0,X1) = X0 | r2_hidden(sK9(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f1])).
% 0.22/0.55  fof(f350,plain,(
% 0.22/0.55    spl10_17 | spl10_6 | ~spl10_10),
% 0.22/0.55    inference(avatar_split_clause,[],[f345,f153,f99,f347])).
% 0.22/0.55  fof(f345,plain,(
% 0.22/0.55    sK1 = sK9(sK1,k2_relat_1(sK2)) | (spl10_6 | ~spl10_10)),
% 0.22/0.55    inference(trivial_inequality_removal,[],[f344])).
% 0.22/0.55  fof(f344,plain,(
% 0.22/0.55    k2_relat_1(sK2) != k2_relat_1(sK2) | sK1 = sK9(sK1,k2_relat_1(sK2)) | (spl10_6 | ~spl10_10)),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f342])).
% 0.22/0.55  fof(f342,plain,(
% 0.22/0.55    k2_relat_1(sK2) != k2_relat_1(sK2) | sK1 = sK9(sK1,k2_relat_1(sK2)) | sK1 = sK9(sK1,k2_relat_1(sK2)) | (spl10_6 | ~spl10_10)),
% 0.22/0.55    inference(resolution,[],[f107,f193])).
% 0.22/0.55  fof(f193,plain,(
% 0.22/0.55    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK2)) | sK1 = X1) ) | ~spl10_10),
% 0.22/0.55    inference(resolution,[],[f167,f46])).
% 0.22/0.55  fof(f46,plain,(
% 0.22/0.55    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK4(X0,X2),X2),X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.22/0.55    inference(equality_resolution,[],[f18])).
% 0.22/0.55  % (6962)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X2),X2),X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,axiom,(
% 0.22/0.55    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.22/0.55  fof(f167,plain,(
% 0.22/0.55    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK2) | sK1 = X3) ) | ~spl10_10),
% 0.22/0.55    inference(superposition,[],[f44,f155])).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_enumset1(X2,X2,X2),k1_enumset1(X3,X3,X3))) | X1 = X3) )),
% 0.22/0.55    inference(definition_unfolding,[],[f32,f34,f34])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (X1 = X3 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f4])).
% 0.22/0.55  fof(f107,plain,(
% 0.22/0.55    ( ! [X0] : (r2_hidden(sK9(sK1,X0),X0) | k2_relat_1(sK2) != X0 | sK1 = sK9(sK1,X0)) ) | spl10_6),
% 0.22/0.55    inference(superposition,[],[f101,f38])).
% 0.22/0.55  fof(f159,plain,(
% 0.22/0.55    spl10_10 | ~spl10_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f70,f61,f153])).
% 0.22/0.55  fof(f61,plain,(
% 0.22/0.55    spl10_2 <=> sK2 = k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.22/0.55  fof(f70,plain,(
% 0.22/0.55    sK2 = k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)) | ~spl10_2),
% 0.22/0.55    inference(superposition,[],[f42,f63])).
% 0.22/0.55  fof(f63,plain,(
% 0.22/0.55    sK2 = k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) | ~spl10_2),
% 0.22/0.55    inference(avatar_component_clause,[],[f61])).
% 0.22/0.55  fof(f42,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)) = k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 0.22/0.55    inference(definition_unfolding,[],[f29,f34,f16,f16])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f5])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 0.22/0.55  fof(f106,plain,(
% 0.22/0.55    ~spl10_6 | ~spl10_7),
% 0.22/0.55    inference(avatar_split_clause,[],[f36,f103,f99])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    k1_relat_1(sK2) != k1_enumset1(sK0,sK0,sK0) | k2_relat_1(sK2) != k1_enumset1(sK1,sK1,sK1)),
% 0.22/0.55    inference(definition_unfolding,[],[f12,f34,f34])).
% 0.22/0.55  fof(f12,plain,(
% 0.22/0.55    k1_tarski(sK0) != k1_relat_1(sK2) | k2_relat_1(sK2) != k1_tarski(sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f11])).
% 0.22/0.55  fof(f11,plain,(
% 0.22/0.55    ? [X0,X1,X2] : ((k2_relat_1(X2) != k1_tarski(X1) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2 & v1_relat_1(X2))),
% 0.22/0.55    inference(flattening,[],[f10])).
% 0.22/0.55  fof(f10,plain,(
% 0.22/0.55    ? [X0,X1,X2] : (((k2_relat_1(X2) != k1_tarski(X1) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2) & v1_relat_1(X2))),
% 0.22/0.55    inference(ennf_transformation,[],[f9])).
% 0.22/0.55  fof(f9,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1,X2] : (v1_relat_1(X2) => (k1_tarski(k4_tarski(X0,X1)) = X2 => (k2_relat_1(X2) = k1_tarski(X1) & k1_tarski(X0) = k1_relat_1(X2))))),
% 0.22/0.55    inference(negated_conjecture,[],[f8])).
% 0.22/0.55  fof(f8,conjecture,(
% 0.22/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => (k1_tarski(k4_tarski(X0,X1)) = X2 => (k2_relat_1(X2) = k1_tarski(X1) & k1_tarski(X0) = k1_relat_1(X2))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relat_1)).
% 0.22/0.55  fof(f97,plain,(
% 0.22/0.55    spl10_5 | ~spl10_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f87,f82,f94])).
% 0.22/0.55  fof(f82,plain,(
% 0.22/0.55    spl10_3 <=> r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.22/0.55  fof(f87,plain,(
% 0.22/0.55    r2_hidden(sK1,k2_relat_1(sK2)) | ~spl10_3),
% 0.22/0.55    inference(resolution,[],[f84,f47])).
% 0.22/0.55  fof(f47,plain,(
% 0.22/0.55    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,k2_relat_1(X0))) )),
% 0.22/0.55    inference(equality_resolution,[],[f17])).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f7])).
% 0.22/0.55  fof(f84,plain,(
% 0.22/0.55    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~spl10_3),
% 0.22/0.55    inference(avatar_component_clause,[],[f82])).
% 0.22/0.55  fof(f92,plain,(
% 0.22/0.55    spl10_4 | ~spl10_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f86,f82,f89])).
% 0.22/0.55  fof(f86,plain,(
% 0.22/0.55    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl10_3),
% 0.22/0.55    inference(resolution,[],[f84,f49])).
% 0.22/0.55  fof(f49,plain,(
% 0.22/0.55    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,k1_relat_1(X0))) )),
% 0.22/0.55    inference(equality_resolution,[],[f21])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f6])).
% 0.22/0.55  fof(f85,plain,(
% 0.22/0.55    spl10_3 | ~spl10_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f78,f61,f82])).
% 0.22/0.55  fof(f78,plain,(
% 0.22/0.55    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~spl10_2),
% 0.22/0.55    inference(superposition,[],[f52,f63])).
% 0.22/0.55  fof(f52,plain,(
% 0.22/0.55    ( ! [X2] : (r2_hidden(X2,k1_enumset1(X2,X2,X2))) )),
% 0.22/0.55    inference(equality_resolution,[],[f51])).
% 0.22/0.55  fof(f51,plain,(
% 0.22/0.55    ( ! [X2,X1] : (r2_hidden(X2,X1) | k1_enumset1(X2,X2,X2) != X1) )),
% 0.22/0.55    inference(equality_resolution,[],[f40])).
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 0.22/0.55    inference(definition_unfolding,[],[f25,f34])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f1])).
% 0.22/0.55  fof(f64,plain,(
% 0.22/0.55    spl10_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f35,f61])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    sK2 = k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),
% 0.22/0.55    inference(definition_unfolding,[],[f14,f34])).
% 0.22/0.55  fof(f14,plain,(
% 0.22/0.55    sK2 = k1_tarski(k4_tarski(sK0,sK1))),
% 0.22/0.55    inference(cnf_transformation,[],[f11])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (6965)------------------------------
% 0.22/0.55  % (6965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (6965)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (6965)Memory used [KB]: 11257
% 0.22/0.55  % (6965)Time elapsed: 0.085 s
% 0.22/0.55  % (6965)------------------------------
% 0.22/0.55  % (6965)------------------------------
% 0.22/0.55  % (6939)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.55  % (6936)Success in time 0.191 s
%------------------------------------------------------------------------------
