%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:58 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 268 expanded)
%              Number of leaves         :   22 (  87 expanded)
%              Depth                    :   14
%              Number of atoms          :  276 ( 991 expanded)
%              Number of equality atoms :   91 ( 266 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f974,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f243,f385,f393,f973])).

fof(f973,plain,(
    ~ spl6_1 ),
    inference(avatar_contradiction_clause,[],[f972])).

fof(f972,plain,
    ( $false
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f969,f770])).

fof(f770,plain,
    ( ! [X3] : k1_xboole_0 != k3_tarski(k1_enumset1(k6_domain_1(k1_xboole_0,sK3(k1_xboole_0)),k6_domain_1(k1_xboole_0,sK3(k1_xboole_0)),X3))
    | ~ spl6_1 ),
    inference(superposition,[],[f101,f412])).

fof(f412,plain,
    ( k6_domain_1(k1_xboole_0,sK3(k1_xboole_0)) = k1_enumset1(sK3(k1_xboole_0),sK3(k1_xboole_0),sK3(k1_xboole_0))
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f297,f162])).

fof(f162,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl6_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f297,plain,(
    k6_domain_1(sK0,sK3(sK0)) = k1_enumset1(sK3(sK0),sK3(sK0),sK3(sK0)) ),
    inference(unit_resulting_resolution,[],[f57,f126,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f81,f99])).

fof(f99,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f64,f73])).

fof(f73,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f64,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f81,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f126,plain,(
    m1_subset_1(sK3(sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f57,f116,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f116,plain,(
    r2_hidden(sK3(sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f57,f69])).

fof(f69,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f57,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( sK0 != sK1
    & r1_tarski(sK0,sK1)
    & v1_zfmisc_1(sK1)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r1_tarski(X0,X1)
            & v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( sK0 != X1
          & r1_tarski(sK0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( sK0 != X1
        & r1_tarski(sK0,X1)
        & v1_zfmisc_1(X1)
        & ~ v1_xboole_0(X1) )
   => ( sK0 != sK1
      & r1_tarski(sK0,sK1)
      & v1_zfmisc_1(sK1)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( r1_tarski(X0,X1)
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f101,plain,(
    ! [X0,X1] : k1_xboole_0 != k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),X1)) ),
    inference(definition_unfolding,[],[f70,f98,f99])).

fof(f98,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f72,f73])).

fof(f72,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f70,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f969,plain,
    ( k1_xboole_0 = k3_tarski(k1_enumset1(k6_domain_1(k1_xboole_0,sK3(k1_xboole_0)),k6_domain_1(k1_xboole_0,sK3(k1_xboole_0)),k1_xboole_0))
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f706,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f80,f98])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f706,plain,
    ( r1_tarski(k6_domain_1(k1_xboole_0,sK3(k1_xboole_0)),k1_xboole_0)
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f411,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f411,plain,
    ( m1_subset_1(k6_domain_1(k1_xboole_0,sK3(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f296,f162])).

fof(f296,plain,(
    m1_subset_1(k6_domain_1(sK0,sK3(sK0)),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f57,f126,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f393,plain,
    ( spl6_1
    | spl6_3
    | spl6_2 ),
    inference(avatar_split_clause,[],[f392,f164,f168,f160])).

fof(f168,plain,
    ( spl6_3
  <=> ! [X0] : sK1 != k1_enumset1(X0,X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f164,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f392,plain,
    ( ! [X0] :
        ( sK1 != k1_enumset1(X0,X0,X0)
        | k1_xboole_0 = sK0 )
    | spl6_2 ),
    inference(subsumption_resolution,[],[f391,f61])).

fof(f61,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f36])).

fof(f391,plain,
    ( ! [X0] :
        ( sK1 != k1_enumset1(X0,X0,X0)
        | k1_xboole_0 = sK0
        | sK0 = sK1 )
    | spl6_2 ),
    inference(subsumption_resolution,[],[f279,f165])).

fof(f165,plain,
    ( k1_xboole_0 != sK1
    | spl6_2 ),
    inference(avatar_component_clause,[],[f164])).

fof(f279,plain,(
    ! [X0] :
      ( sK1 != k1_enumset1(X0,X0,X0)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | sK0 = sK1 ) ),
    inference(superposition,[],[f112,f122])).

fof(f122,plain,(
    sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f60,f104])).

fof(f60,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k1_enumset1(X0,X0,X0) != k3_tarski(k1_enumset1(X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f96,f99,f98])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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

fof(f385,plain,(
    ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f366])).

fof(f366,plain,
    ( $false
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f169,f139])).

fof(f139,plain,(
    sK1 = k1_enumset1(sK2(sK1),sK2(sK1),sK2(sK1)) ),
    inference(forward_demodulation,[],[f137,f119])).

fof(f119,plain,(
    sK1 = k6_domain_1(sK1,sK2(sK1)) ),
    inference(unit_resulting_resolution,[],[f58,f59,f66])).

fof(f66,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK2(X0)) = X0
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK2(X0)) = X0
            & m1_subset_1(sK2(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK2(X0)) = X0
        & m1_subset_1(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X2] :
              ( k6_domain_1(X0,X2) = X0
              & m1_subset_1(X2,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X1] :
              ( k6_domain_1(X0,X1) = X0
              & m1_subset_1(X1,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

fof(f59,plain,(
    v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f58,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f137,plain,(
    k6_domain_1(sK1,sK2(sK1)) = k1_enumset1(sK2(sK1),sK2(sK1),sK2(sK1)) ),
    inference(unit_resulting_resolution,[],[f58,f118,f105])).

fof(f118,plain,(
    m1_subset_1(sK2(sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f58,f59,f65])).

fof(f65,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f169,plain,
    ( ! [X0] : sK1 != k1_enumset1(X0,X0,X0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f168])).

fof(f243,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f242])).

fof(f242,plain,
    ( $false
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f236,f161])).

fof(f161,plain,
    ( k1_xboole_0 != sK0
    | spl6_1 ),
    inference(avatar_component_clause,[],[f160])).

fof(f236,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_2 ),
    inference(superposition,[],[f62,f178])).

fof(f178,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f120,f166])).

fof(f166,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f164])).

fof(f120,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f60,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f62,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:50:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.20/0.52  % (13377)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.20/0.52  % (13386)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.20/0.52  % (13374)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.20/0.52  % (13369)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.20/0.52  % (13386)Refutation not found, incomplete strategy% (13386)------------------------------
% 1.20/0.52  % (13386)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.52  % (13386)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.52  
% 1.20/0.52  % (13386)Memory used [KB]: 10746
% 1.20/0.52  % (13386)Time elapsed: 0.057 s
% 1.20/0.52  % (13386)------------------------------
% 1.20/0.52  % (13386)------------------------------
% 1.20/0.53  % (13372)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.20/0.53  % (13385)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.20/0.53  % (13381)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.41/0.54  % (13366)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.41/0.54  % (13365)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.41/0.54  % (13393)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.41/0.54  % (13366)Refutation not found, incomplete strategy% (13366)------------------------------
% 1.41/0.54  % (13366)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (13366)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (13366)Memory used [KB]: 10746
% 1.41/0.54  % (13366)Time elapsed: 0.129 s
% 1.41/0.54  % (13366)------------------------------
% 1.41/0.54  % (13366)------------------------------
% 1.41/0.54  % (13378)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.41/0.54  % (13374)Refutation not found, incomplete strategy% (13374)------------------------------
% 1.41/0.54  % (13374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (13374)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (13374)Memory used [KB]: 10618
% 1.41/0.54  % (13374)Time elapsed: 0.136 s
% 1.41/0.54  % (13374)------------------------------
% 1.41/0.54  % (13374)------------------------------
% 1.41/0.54  % (13364)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.41/0.54  % (13390)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.41/0.54  % (13370)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.41/0.54  % (13368)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.41/0.54  % (13381)Refutation not found, incomplete strategy% (13381)------------------------------
% 1.41/0.54  % (13381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (13380)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.41/0.55  % (13381)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (13381)Memory used [KB]: 10618
% 1.41/0.55  % (13381)Time elapsed: 0.143 s
% 1.41/0.55  % (13381)------------------------------
% 1.41/0.55  % (13381)------------------------------
% 1.41/0.55  % (13379)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.41/0.55  % (13373)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.41/0.55  % (13383)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.41/0.56  % (13367)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.41/0.56  % (13371)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.41/0.56  % (13389)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.41/0.56  % (13387)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.41/0.56  % (13392)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.41/0.57  % (13375)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.41/0.57  % (13376)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.41/0.57  % (13375)Refutation not found, incomplete strategy% (13375)------------------------------
% 1.41/0.57  % (13375)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.57  % (13375)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.57  
% 1.41/0.57  % (13375)Memory used [KB]: 10618
% 1.41/0.57  % (13375)Time elapsed: 0.161 s
% 1.41/0.57  % (13375)------------------------------
% 1.41/0.57  % (13375)------------------------------
% 1.41/0.57  % (13391)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.41/0.57  % (13384)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.41/0.58  % (13382)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.41/0.58  % (13388)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.41/0.60  % (13373)Refutation not found, incomplete strategy% (13373)------------------------------
% 1.41/0.60  % (13373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.60  % (13373)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.60  
% 1.41/0.60  % (13373)Memory used [KB]: 10874
% 1.41/0.60  % (13373)Time elapsed: 0.190 s
% 1.41/0.60  % (13373)------------------------------
% 1.41/0.60  % (13373)------------------------------
% 1.41/0.62  % (13390)Refutation found. Thanks to Tanya!
% 1.41/0.62  % SZS status Theorem for theBenchmark
% 1.41/0.62  % SZS output start Proof for theBenchmark
% 1.41/0.62  fof(f974,plain,(
% 1.41/0.62    $false),
% 1.41/0.62    inference(avatar_sat_refutation,[],[f243,f385,f393,f973])).
% 1.41/0.62  fof(f973,plain,(
% 1.41/0.62    ~spl6_1),
% 1.41/0.62    inference(avatar_contradiction_clause,[],[f972])).
% 1.41/0.62  fof(f972,plain,(
% 1.41/0.62    $false | ~spl6_1),
% 1.41/0.62    inference(subsumption_resolution,[],[f969,f770])).
% 1.41/0.62  fof(f770,plain,(
% 1.41/0.62    ( ! [X3] : (k1_xboole_0 != k3_tarski(k1_enumset1(k6_domain_1(k1_xboole_0,sK3(k1_xboole_0)),k6_domain_1(k1_xboole_0,sK3(k1_xboole_0)),X3))) ) | ~spl6_1),
% 1.41/0.62    inference(superposition,[],[f101,f412])).
% 1.41/0.62  fof(f412,plain,(
% 1.41/0.62    k6_domain_1(k1_xboole_0,sK3(k1_xboole_0)) = k1_enumset1(sK3(k1_xboole_0),sK3(k1_xboole_0),sK3(k1_xboole_0)) | ~spl6_1),
% 1.41/0.62    inference(backward_demodulation,[],[f297,f162])).
% 1.41/0.62  fof(f162,plain,(
% 1.41/0.62    k1_xboole_0 = sK0 | ~spl6_1),
% 1.41/0.62    inference(avatar_component_clause,[],[f160])).
% 1.41/0.62  fof(f160,plain,(
% 1.41/0.62    spl6_1 <=> k1_xboole_0 = sK0),
% 1.41/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.41/0.62  fof(f297,plain,(
% 1.41/0.62    k6_domain_1(sK0,sK3(sK0)) = k1_enumset1(sK3(sK0),sK3(sK0),sK3(sK0))),
% 1.41/0.62    inference(unit_resulting_resolution,[],[f57,f126,f105])).
% 1.41/0.62  fof(f105,plain,(
% 1.41/0.62    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.41/0.62    inference(definition_unfolding,[],[f81,f99])).
% 1.41/0.62  fof(f99,plain,(
% 1.41/0.62    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.41/0.62    inference(definition_unfolding,[],[f64,f73])).
% 1.41/0.62  fof(f73,plain,(
% 1.41/0.62    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.41/0.62    inference(cnf_transformation,[],[f11])).
% 1.41/0.62  fof(f11,axiom,(
% 1.41/0.62    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.41/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.41/0.62  fof(f64,plain,(
% 1.41/0.62    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.41/0.62    inference(cnf_transformation,[],[f10])).
% 1.41/0.62  fof(f10,axiom,(
% 1.41/0.62    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.41/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.41/0.62  fof(f81,plain,(
% 1.41/0.62    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.41/0.62    inference(cnf_transformation,[],[f29])).
% 1.41/0.62  fof(f29,plain,(
% 1.41/0.62    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.41/0.62    inference(flattening,[],[f28])).
% 1.41/0.62  fof(f28,plain,(
% 1.41/0.62    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.41/0.62    inference(ennf_transformation,[],[f19])).
% 1.41/0.62  fof(f19,axiom,(
% 1.41/0.62    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.41/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.41/0.62  fof(f126,plain,(
% 1.41/0.62    m1_subset_1(sK3(sK0),sK0)),
% 1.41/0.62    inference(unit_resulting_resolution,[],[f57,f116,f77])).
% 1.41/0.62  fof(f77,plain,(
% 1.41/0.62    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.41/0.62    inference(cnf_transformation,[],[f45])).
% 1.41/0.62  fof(f45,plain,(
% 1.41/0.62    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.41/0.62    inference(nnf_transformation,[],[f26])).
% 1.41/0.62  fof(f26,plain,(
% 1.41/0.62    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.41/0.62    inference(ennf_transformation,[],[f15])).
% 1.41/0.62  fof(f15,axiom,(
% 1.41/0.62    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.41/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.41/0.62  fof(f116,plain,(
% 1.41/0.62    r2_hidden(sK3(sK0),sK0)),
% 1.41/0.62    inference(unit_resulting_resolution,[],[f57,f69])).
% 1.41/0.62  fof(f69,plain,(
% 1.41/0.62    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) )),
% 1.41/0.62    inference(cnf_transformation,[],[f44])).
% 1.41/0.62  fof(f44,plain,(
% 1.41/0.62    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.41/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f43])).
% 1.41/0.62  fof(f43,plain,(
% 1.41/0.62    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.41/0.62    introduced(choice_axiom,[])).
% 1.41/0.62  fof(f42,plain,(
% 1.41/0.62    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.41/0.62    inference(rectify,[],[f41])).
% 1.41/0.62  fof(f41,plain,(
% 1.41/0.62    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.41/0.62    inference(nnf_transformation,[],[f1])).
% 1.41/0.62  fof(f1,axiom,(
% 1.41/0.62    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.41/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.41/0.62  fof(f57,plain,(
% 1.41/0.62    ~v1_xboole_0(sK0)),
% 1.41/0.62    inference(cnf_transformation,[],[f36])).
% 1.41/0.62  fof(f36,plain,(
% 1.41/0.62    (sK0 != sK1 & r1_tarski(sK0,sK1) & v1_zfmisc_1(sK1) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 1.41/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f35,f34])).
% 1.41/0.62  fof(f34,plain,(
% 1.41/0.62    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (sK0 != X1 & r1_tarski(sK0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 1.41/0.62    introduced(choice_axiom,[])).
% 1.41/0.62  fof(f35,plain,(
% 1.41/0.62    ? [X1] : (sK0 != X1 & r1_tarski(sK0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (sK0 != sK1 & r1_tarski(sK0,sK1) & v1_zfmisc_1(sK1) & ~v1_xboole_0(sK1))),
% 1.41/0.62    introduced(choice_axiom,[])).
% 1.41/0.62  fof(f24,plain,(
% 1.41/0.62    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.41/0.62    inference(flattening,[],[f23])).
% 1.41/0.62  fof(f23,plain,(
% 1.41/0.62    ? [X0] : (? [X1] : ((X0 != X1 & r1_tarski(X0,X1)) & (v1_zfmisc_1(X1) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 1.41/0.62    inference(ennf_transformation,[],[f22])).
% 1.41/0.62  fof(f22,negated_conjecture,(
% 1.41/0.62    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.41/0.62    inference(negated_conjecture,[],[f21])).
% 1.41/0.62  fof(f21,conjecture,(
% 1.41/0.62    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.41/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 1.41/0.62  fof(f101,plain,(
% 1.41/0.62    ( ! [X0,X1] : (k1_xboole_0 != k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),X1))) )),
% 1.41/0.62    inference(definition_unfolding,[],[f70,f98,f99])).
% 1.41/0.62  fof(f98,plain,(
% 1.41/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 1.41/0.62    inference(definition_unfolding,[],[f72,f73])).
% 1.41/0.62  fof(f72,plain,(
% 1.41/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.41/0.62    inference(cnf_transformation,[],[f12])).
% 1.41/0.62  fof(f12,axiom,(
% 1.41/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.41/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.41/0.62  fof(f70,plain,(
% 1.41/0.62    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 1.41/0.62    inference(cnf_transformation,[],[f14])).
% 1.41/0.62  fof(f14,axiom,(
% 1.41/0.62    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.41/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.41/0.62  fof(f969,plain,(
% 1.41/0.62    k1_xboole_0 = k3_tarski(k1_enumset1(k6_domain_1(k1_xboole_0,sK3(k1_xboole_0)),k6_domain_1(k1_xboole_0,sK3(k1_xboole_0)),k1_xboole_0)) | ~spl6_1),
% 1.41/0.62    inference(unit_resulting_resolution,[],[f706,f104])).
% 1.41/0.62  fof(f104,plain,(
% 1.41/0.62    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 1.41/0.62    inference(definition_unfolding,[],[f80,f98])).
% 1.41/0.62  fof(f80,plain,(
% 1.41/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.41/0.62    inference(cnf_transformation,[],[f27])).
% 1.41/0.62  fof(f27,plain,(
% 1.41/0.62    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.41/0.62    inference(ennf_transformation,[],[f5])).
% 1.41/0.62  fof(f5,axiom,(
% 1.41/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.41/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.41/0.62  fof(f706,plain,(
% 1.41/0.62    r1_tarski(k6_domain_1(k1_xboole_0,sK3(k1_xboole_0)),k1_xboole_0) | ~spl6_1),
% 1.41/0.62    inference(unit_resulting_resolution,[],[f411,f86])).
% 1.41/0.62  fof(f86,plain,(
% 1.41/0.62    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.41/0.62    inference(cnf_transformation,[],[f50])).
% 1.41/0.62  fof(f50,plain,(
% 1.41/0.62    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.41/0.62    inference(nnf_transformation,[],[f17])).
% 1.41/0.62  fof(f17,axiom,(
% 1.41/0.62    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.41/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.41/0.62  fof(f411,plain,(
% 1.41/0.62    m1_subset_1(k6_domain_1(k1_xboole_0,sK3(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) | ~spl6_1),
% 1.41/0.62    inference(backward_demodulation,[],[f296,f162])).
% 1.41/0.62  fof(f296,plain,(
% 1.41/0.62    m1_subset_1(k6_domain_1(sK0,sK3(sK0)),k1_zfmisc_1(sK0))),
% 1.41/0.62    inference(unit_resulting_resolution,[],[f57,f126,f82])).
% 1.41/0.62  fof(f82,plain,(
% 1.41/0.62    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.41/0.62    inference(cnf_transformation,[],[f31])).
% 1.41/0.62  fof(f31,plain,(
% 1.41/0.62    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.41/0.62    inference(flattening,[],[f30])).
% 1.41/0.62  fof(f30,plain,(
% 1.41/0.62    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.41/0.62    inference(ennf_transformation,[],[f18])).
% 1.41/0.62  fof(f18,axiom,(
% 1.41/0.62    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.41/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 1.41/0.62  fof(f393,plain,(
% 1.41/0.62    spl6_1 | spl6_3 | spl6_2),
% 1.41/0.62    inference(avatar_split_clause,[],[f392,f164,f168,f160])).
% 1.41/0.62  fof(f168,plain,(
% 1.41/0.62    spl6_3 <=> ! [X0] : sK1 != k1_enumset1(X0,X0,X0)),
% 1.41/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.41/0.62  fof(f164,plain,(
% 1.41/0.62    spl6_2 <=> k1_xboole_0 = sK1),
% 1.41/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.41/0.62  fof(f392,plain,(
% 1.41/0.62    ( ! [X0] : (sK1 != k1_enumset1(X0,X0,X0) | k1_xboole_0 = sK0) ) | spl6_2),
% 1.41/0.62    inference(subsumption_resolution,[],[f391,f61])).
% 1.41/0.62  fof(f61,plain,(
% 1.41/0.62    sK0 != sK1),
% 1.41/0.62    inference(cnf_transformation,[],[f36])).
% 1.41/0.62  fof(f391,plain,(
% 1.41/0.62    ( ! [X0] : (sK1 != k1_enumset1(X0,X0,X0) | k1_xboole_0 = sK0 | sK0 = sK1) ) | spl6_2),
% 1.41/0.62    inference(subsumption_resolution,[],[f279,f165])).
% 1.41/0.62  fof(f165,plain,(
% 1.41/0.62    k1_xboole_0 != sK1 | spl6_2),
% 1.41/0.62    inference(avatar_component_clause,[],[f164])).
% 1.41/0.62  fof(f279,plain,(
% 1.41/0.62    ( ! [X0] : (sK1 != k1_enumset1(X0,X0,X0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK0 = sK1) )),
% 1.41/0.62    inference(superposition,[],[f112,f122])).
% 1.41/0.62  fof(f122,plain,(
% 1.41/0.62    sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1))),
% 1.41/0.62    inference(unit_resulting_resolution,[],[f60,f104])).
% 1.41/0.62  fof(f60,plain,(
% 1.41/0.62    r1_tarski(sK0,sK1)),
% 1.41/0.62    inference(cnf_transformation,[],[f36])).
% 1.41/0.62  fof(f112,plain,(
% 1.41/0.62    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k1_enumset1(X0,X0,X0) != k3_tarski(k1_enumset1(X1,X1,X2))) )),
% 1.41/0.62    inference(definition_unfolding,[],[f96,f99,f98])).
% 1.41/0.62  fof(f96,plain,(
% 1.41/0.62    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k1_tarski(X0) != k2_xboole_0(X1,X2)) )),
% 1.41/0.62    inference(cnf_transformation,[],[f33])).
% 1.41/0.62  fof(f33,plain,(
% 1.41/0.62    ! [X0,X1,X2] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k1_tarski(X0) != k2_xboole_0(X1,X2))),
% 1.41/0.62    inference(ennf_transformation,[],[f13])).
% 1.41/0.62  fof(f13,axiom,(
% 1.41/0.62    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.41/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 1.41/0.62  fof(f385,plain,(
% 1.41/0.62    ~spl6_3),
% 1.41/0.62    inference(avatar_contradiction_clause,[],[f366])).
% 1.41/0.62  fof(f366,plain,(
% 1.41/0.62    $false | ~spl6_3),
% 1.41/0.62    inference(unit_resulting_resolution,[],[f169,f139])).
% 1.41/0.62  fof(f139,plain,(
% 1.41/0.62    sK1 = k1_enumset1(sK2(sK1),sK2(sK1),sK2(sK1))),
% 1.41/0.62    inference(forward_demodulation,[],[f137,f119])).
% 1.41/0.62  fof(f119,plain,(
% 1.41/0.62    sK1 = k6_domain_1(sK1,sK2(sK1))),
% 1.41/0.62    inference(unit_resulting_resolution,[],[f58,f59,f66])).
% 1.41/0.62  fof(f66,plain,(
% 1.41/0.62    ( ! [X0] : (k6_domain_1(X0,sK2(X0)) = X0 | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 1.41/0.62    inference(cnf_transformation,[],[f40])).
% 1.41/0.62  fof(f40,plain,(
% 1.41/0.62    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK2(X0)) = X0 & m1_subset_1(sK2(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 1.41/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).
% 1.41/0.62  fof(f39,plain,(
% 1.41/0.62    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK2(X0)) = X0 & m1_subset_1(sK2(X0),X0)))),
% 1.41/0.62    introduced(choice_axiom,[])).
% 1.41/0.62  fof(f38,plain,(
% 1.41/0.62    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 1.41/0.62    inference(rectify,[],[f37])).
% 1.41/0.62  fof(f37,plain,(
% 1.41/0.62    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 1.41/0.62    inference(nnf_transformation,[],[f25])).
% 1.41/0.62  fof(f25,plain,(
% 1.41/0.62    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 1.41/0.62    inference(ennf_transformation,[],[f20])).
% 1.41/0.62  fof(f20,axiom,(
% 1.41/0.62    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 1.41/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).
% 1.41/0.62  fof(f59,plain,(
% 1.41/0.62    v1_zfmisc_1(sK1)),
% 1.41/0.62    inference(cnf_transformation,[],[f36])).
% 1.41/0.62  fof(f58,plain,(
% 1.41/0.62    ~v1_xboole_0(sK1)),
% 1.41/0.62    inference(cnf_transformation,[],[f36])).
% 1.41/0.62  fof(f137,plain,(
% 1.41/0.62    k6_domain_1(sK1,sK2(sK1)) = k1_enumset1(sK2(sK1),sK2(sK1),sK2(sK1))),
% 1.41/0.62    inference(unit_resulting_resolution,[],[f58,f118,f105])).
% 1.41/0.62  fof(f118,plain,(
% 1.41/0.62    m1_subset_1(sK2(sK1),sK1)),
% 1.41/0.62    inference(unit_resulting_resolution,[],[f58,f59,f65])).
% 1.41/0.62  fof(f65,plain,(
% 1.41/0.62    ( ! [X0] : (m1_subset_1(sK2(X0),X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 1.41/0.62    inference(cnf_transformation,[],[f40])).
% 1.41/0.62  fof(f169,plain,(
% 1.41/0.62    ( ! [X0] : (sK1 != k1_enumset1(X0,X0,X0)) ) | ~spl6_3),
% 1.41/0.62    inference(avatar_component_clause,[],[f168])).
% 1.41/0.62  fof(f243,plain,(
% 1.41/0.62    spl6_1 | ~spl6_2),
% 1.41/0.62    inference(avatar_contradiction_clause,[],[f242])).
% 1.41/0.62  fof(f242,plain,(
% 1.41/0.62    $false | (spl6_1 | ~spl6_2)),
% 1.41/0.62    inference(subsumption_resolution,[],[f236,f161])).
% 1.41/0.62  fof(f161,plain,(
% 1.41/0.62    k1_xboole_0 != sK0 | spl6_1),
% 1.41/0.62    inference(avatar_component_clause,[],[f160])).
% 1.41/0.62  fof(f236,plain,(
% 1.41/0.62    k1_xboole_0 = sK0 | ~spl6_2),
% 1.41/0.62    inference(superposition,[],[f62,f178])).
% 1.41/0.62  fof(f178,plain,(
% 1.41/0.62    k1_xboole_0 = k4_xboole_0(sK0,k1_xboole_0) | ~spl6_2),
% 1.41/0.62    inference(backward_demodulation,[],[f120,f166])).
% 1.41/0.62  fof(f166,plain,(
% 1.41/0.62    k1_xboole_0 = sK1 | ~spl6_2),
% 1.41/0.62    inference(avatar_component_clause,[],[f164])).
% 1.41/0.62  fof(f120,plain,(
% 1.41/0.62    k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 1.41/0.62    inference(unit_resulting_resolution,[],[f60,f89])).
% 1.41/0.62  fof(f89,plain,(
% 1.41/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.41/0.62    inference(cnf_transformation,[],[f51])).
% 1.41/0.62  fof(f51,plain,(
% 1.41/0.62    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.41/0.62    inference(nnf_transformation,[],[f4])).
% 1.41/0.62  fof(f4,axiom,(
% 1.41/0.62    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.41/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.41/0.62  fof(f62,plain,(
% 1.41/0.62    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.41/0.62    inference(cnf_transformation,[],[f8])).
% 1.41/0.62  fof(f8,axiom,(
% 1.41/0.62    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.41/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.41/0.62  % SZS output end Proof for theBenchmark
% 1.41/0.62  % (13390)------------------------------
% 1.41/0.62  % (13390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.62  % (13390)Termination reason: Refutation
% 1.41/0.62  
% 1.41/0.62  % (13390)Memory used [KB]: 11257
% 1.41/0.62  % (13390)Time elapsed: 0.208 s
% 1.41/0.62  % (13390)------------------------------
% 1.41/0.62  % (13390)------------------------------
% 1.41/0.63  % (13363)Success in time 0.26 s
%------------------------------------------------------------------------------
