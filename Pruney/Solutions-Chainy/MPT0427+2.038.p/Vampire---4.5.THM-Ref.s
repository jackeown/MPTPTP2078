%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:38 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 209 expanded)
%              Number of leaves         :   21 (  63 expanded)
%              Depth                    :   14
%              Number of atoms          :  291 ( 691 expanded)
%              Number of equality atoms :   52 ( 116 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f329,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f230,f239,f263,f289,f306,f328])).

fof(f328,plain,
    ( ~ spl6_4
    | ~ spl6_7 ),
    inference(avatar_contradiction_clause,[],[f327])).

fof(f327,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f326,f301])).

fof(f301,plain,
    ( m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f300,f42])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f29,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
            & r1_tarski(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1))
          & r1_tarski(sK1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1))
        & r1_tarski(sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
   => ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

fof(f300,plain,
    ( m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl6_7 ),
    inference(superposition,[],[f53,f238])).

fof(f238,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl6_7
  <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(f326,plain,
    ( ~ m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(resolution,[],[f323,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f323,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK0)
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f322,f238])).

fof(f322,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),sK0)
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f321,f78])).

fof(f78,plain,(
    ! [X0] : k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(subsumption_resolution,[],[f64,f45])).

fof(f45,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f64,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f321,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0))
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f44,f225])).

fof(f225,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f223])).

fof(f223,plain,
    ( spl6_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f44,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f306,plain,
    ( spl6_4
    | ~ spl6_5
    | ~ spl6_7 ),
    inference(avatar_contradiction_clause,[],[f305])).

fof(f305,plain,
    ( $false
    | spl6_4
    | ~ spl6_5
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f304,f43])).

fof(f43,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f304,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl6_4
    | ~ spl6_5
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f302,f224])).

fof(f224,plain,
    ( k1_xboole_0 != sK1
    | spl6_4 ),
    inference(avatar_component_clause,[],[f223])).

fof(f302,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,sK2)
    | ~ spl6_5
    | ~ spl6_7 ),
    inference(resolution,[],[f299,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f299,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | ~ spl6_5
    | ~ spl6_7 ),
    inference(backward_demodulation,[],[f295,f238])).

fof(f295,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1))
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f44,f229])).

fof(f229,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl6_5
  <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f289,plain,
    ( spl6_4
    | ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f288])).

fof(f288,plain,
    ( $false
    | spl6_4
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f283,f224])).

fof(f283,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_6 ),
    inference(resolution,[],[f282,f47])).

fof(f47,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f282,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl6_6 ),
    inference(resolution,[],[f280,f89])).

fof(f89,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X4,k1_xboole_0)
      | ~ r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f84,f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f84,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(condensation,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(trivial_inequality_removal,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f70,f46])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X2,X1) != X2
      | ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f50,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f280,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f43,f234])).

fof(f234,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl6_6
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f263,plain,
    ( ~ spl6_4
    | ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f262])).

fof(f262,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f261,f69])).

fof(f69,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f60,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f261,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f260,f78])).

fof(f260,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,k1_xboole_0),sK0)
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f251,f234])).

fof(f251,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),sK0)
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f243,f78])).

fof(f243,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0))
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f44,f225])).

fof(f239,plain,
    ( spl6_6
    | spl6_7 ),
    inference(avatar_split_clause,[],[f215,f236,f232])).

fof(f215,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f152,f42])).

fof(f152,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k8_setfam_1(X0,X1) = k1_setfam_1(X1)
      | k1_xboole_0 = X1 ) ),
    inference(duplicate_literal_removal,[],[f151])).

fof(f151,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(superposition,[],[f52,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f230,plain,
    ( spl6_4
    | spl6_5 ),
    inference(avatar_split_clause,[],[f214,f227,f223])).

fof(f214,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f152,f41])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:29:29 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.52  % (29855)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.23/0.53  % (29845)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.23/0.53  % (29846)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.23/0.53  % (29863)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.23/0.54  % (29868)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.23/0.54  % (29847)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.55  % (29849)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.23/0.55  % (29851)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.23/0.55  % (29860)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.23/0.55  % (29848)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.23/0.55  % (29853)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.23/0.55  % (29852)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.23/0.55  % (29853)Refutation not found, incomplete strategy% (29853)------------------------------
% 0.23/0.55  % (29853)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (29865)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.23/0.56  % (29854)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.23/0.56  % (29874)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.23/0.56  % (29873)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.23/0.56  % (29848)Refutation found. Thanks to Tanya!
% 0.23/0.56  % SZS status Theorem for theBenchmark
% 0.23/0.56  % (29853)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (29853)Memory used [KB]: 10746
% 0.23/0.56  % (29853)Time elapsed: 0.135 s
% 0.23/0.56  % (29853)------------------------------
% 0.23/0.56  % (29853)------------------------------
% 0.23/0.56  % (29870)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.23/0.56  % (29864)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.23/0.56  % (29867)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.23/0.56  % (29857)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.56  % (29859)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.23/0.56  % (29862)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.23/0.56  % (29872)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.23/0.56  % (29871)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.23/0.57  % (29850)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.23/0.57  % (29861)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.23/0.57  % (29869)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.23/0.57  % (29856)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.59/0.57  % SZS output start Proof for theBenchmark
% 1.59/0.57  fof(f329,plain,(
% 1.59/0.57    $false),
% 1.59/0.57    inference(avatar_sat_refutation,[],[f230,f239,f263,f289,f306,f328])).
% 1.59/0.57  fof(f328,plain,(
% 1.59/0.57    ~spl6_4 | ~spl6_7),
% 1.59/0.57    inference(avatar_contradiction_clause,[],[f327])).
% 1.59/0.57  fof(f327,plain,(
% 1.59/0.57    $false | (~spl6_4 | ~spl6_7)),
% 1.59/0.57    inference(subsumption_resolution,[],[f326,f301])).
% 1.59/0.57  fof(f301,plain,(
% 1.59/0.57    m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | ~spl6_7),
% 1.59/0.57    inference(subsumption_resolution,[],[f300,f42])).
% 1.59/0.57  fof(f42,plain,(
% 1.59/0.57    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.59/0.57    inference(cnf_transformation,[],[f30])).
% 1.59/0.57  fof(f30,plain,(
% 1.59/0.57    (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.59/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f29,f28])).
% 1.59/0.57  fof(f28,plain,(
% 1.59/0.57    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 1.59/0.57    introduced(choice_axiom,[])).
% 1.59/0.57  fof(f29,plain,(
% 1.59/0.57    ? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) => (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 1.59/0.57    introduced(choice_axiom,[])).
% 1.59/0.57  fof(f17,plain,(
% 1.59/0.57    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.59/0.57    inference(flattening,[],[f16])).
% 1.59/0.57  fof(f16,plain,(
% 1.59/0.57    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.59/0.57    inference(ennf_transformation,[],[f14])).
% 1.59/0.57  fof(f14,negated_conjecture,(
% 1.59/0.57    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 1.59/0.57    inference(negated_conjecture,[],[f13])).
% 1.59/0.57  fof(f13,conjecture,(
% 1.59/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 1.59/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).
% 1.59/0.57  fof(f300,plain,(
% 1.59/0.57    m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl6_7),
% 1.59/0.57    inference(superposition,[],[f53,f238])).
% 1.59/0.57  fof(f238,plain,(
% 1.59/0.57    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl6_7),
% 1.59/0.57    inference(avatar_component_clause,[],[f236])).
% 1.59/0.57  fof(f236,plain,(
% 1.59/0.57    spl6_7 <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 1.59/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.59/0.57  fof(f53,plain,(
% 1.59/0.57    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.59/0.57    inference(cnf_transformation,[],[f23])).
% 1.59/0.57  fof(f23,plain,(
% 1.59/0.57    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.59/0.57    inference(ennf_transformation,[],[f8])).
% 1.59/0.57  fof(f8,axiom,(
% 1.59/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.59/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).
% 1.59/0.57  fof(f326,plain,(
% 1.59/0.57    ~m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | (~spl6_4 | ~spl6_7)),
% 1.59/0.57    inference(resolution,[],[f323,f61])).
% 1.59/0.57  fof(f61,plain,(
% 1.59/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.59/0.57    inference(cnf_transformation,[],[f40])).
% 1.59/0.57  fof(f40,plain,(
% 1.59/0.57    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.59/0.57    inference(nnf_transformation,[],[f10])).
% 1.59/0.57  fof(f10,axiom,(
% 1.59/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.59/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.59/0.57  fof(f323,plain,(
% 1.59/0.57    ~r1_tarski(k1_setfam_1(sK2),sK0) | (~spl6_4 | ~spl6_7)),
% 1.59/0.57    inference(forward_demodulation,[],[f322,f238])).
% 1.59/0.57  fof(f322,plain,(
% 1.59/0.57    ~r1_tarski(k8_setfam_1(sK0,sK2),sK0) | ~spl6_4),
% 1.59/0.57    inference(forward_demodulation,[],[f321,f78])).
% 1.59/0.57  fof(f78,plain,(
% 1.59/0.57    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 1.59/0.57    inference(subsumption_resolution,[],[f64,f45])).
% 1.59/0.57  fof(f45,plain,(
% 1.59/0.57    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.59/0.57    inference(cnf_transformation,[],[f6])).
% 1.59/0.57  fof(f6,axiom,(
% 1.59/0.57    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.59/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.59/0.57  fof(f64,plain,(
% 1.59/0.57    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.59/0.57    inference(equality_resolution,[],[f55])).
% 1.59/0.57  fof(f55,plain,(
% 1.59/0.57    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.59/0.57    inference(cnf_transformation,[],[f24])).
% 1.59/0.57  fof(f24,plain,(
% 1.59/0.57    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.59/0.57    inference(ennf_transformation,[],[f7])).
% 1.59/0.57  fof(f7,axiom,(
% 1.59/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 1.59/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).
% 1.59/0.57  fof(f321,plain,(
% 1.59/0.57    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) | ~spl6_4),
% 1.59/0.57    inference(forward_demodulation,[],[f44,f225])).
% 1.59/0.57  fof(f225,plain,(
% 1.59/0.57    k1_xboole_0 = sK1 | ~spl6_4),
% 1.59/0.57    inference(avatar_component_clause,[],[f223])).
% 1.59/0.57  fof(f223,plain,(
% 1.59/0.57    spl6_4 <=> k1_xboole_0 = sK1),
% 1.59/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.59/0.57  fof(f44,plain,(
% 1.59/0.57    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 1.59/0.57    inference(cnf_transformation,[],[f30])).
% 1.59/0.57  fof(f306,plain,(
% 1.59/0.57    spl6_4 | ~spl6_5 | ~spl6_7),
% 1.59/0.57    inference(avatar_contradiction_clause,[],[f305])).
% 1.59/0.57  fof(f305,plain,(
% 1.59/0.57    $false | (spl6_4 | ~spl6_5 | ~spl6_7)),
% 1.59/0.57    inference(subsumption_resolution,[],[f304,f43])).
% 1.59/0.57  fof(f43,plain,(
% 1.59/0.57    r1_tarski(sK1,sK2)),
% 1.59/0.57    inference(cnf_transformation,[],[f30])).
% 1.59/0.57  fof(f304,plain,(
% 1.59/0.57    ~r1_tarski(sK1,sK2) | (spl6_4 | ~spl6_5 | ~spl6_7)),
% 1.59/0.57    inference(subsumption_resolution,[],[f302,f224])).
% 1.59/0.57  fof(f224,plain,(
% 1.59/0.57    k1_xboole_0 != sK1 | spl6_4),
% 1.59/0.57    inference(avatar_component_clause,[],[f223])).
% 1.59/0.57  fof(f302,plain,(
% 1.59/0.57    k1_xboole_0 = sK1 | ~r1_tarski(sK1,sK2) | (~spl6_5 | ~spl6_7)),
% 1.59/0.57    inference(resolution,[],[f299,f51])).
% 1.59/0.57  fof(f51,plain,(
% 1.59/0.57    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f21])).
% 1.59/0.57  fof(f21,plain,(
% 1.59/0.57    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 1.59/0.57    inference(flattening,[],[f20])).
% 1.59/0.57  fof(f20,plain,(
% 1.59/0.57    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 1.59/0.57    inference(ennf_transformation,[],[f12])).
% 1.59/0.57  fof(f12,axiom,(
% 1.59/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 1.59/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).
% 1.59/0.57  fof(f299,plain,(
% 1.59/0.57    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | (~spl6_5 | ~spl6_7)),
% 1.59/0.57    inference(backward_demodulation,[],[f295,f238])).
% 1.59/0.57  fof(f295,plain,(
% 1.59/0.57    ~r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1)) | ~spl6_5),
% 1.59/0.57    inference(backward_demodulation,[],[f44,f229])).
% 1.59/0.58  fof(f229,plain,(
% 1.59/0.58    k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | ~spl6_5),
% 1.59/0.58    inference(avatar_component_clause,[],[f227])).
% 1.59/0.58  fof(f227,plain,(
% 1.59/0.58    spl6_5 <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.59/0.58  fof(f289,plain,(
% 1.59/0.58    spl6_4 | ~spl6_6),
% 1.59/0.58    inference(avatar_contradiction_clause,[],[f288])).
% 1.59/0.58  fof(f288,plain,(
% 1.59/0.58    $false | (spl6_4 | ~spl6_6)),
% 1.59/0.58    inference(subsumption_resolution,[],[f283,f224])).
% 1.59/0.58  fof(f283,plain,(
% 1.59/0.58    k1_xboole_0 = sK1 | ~spl6_6),
% 1.59/0.58    inference(resolution,[],[f282,f47])).
% 1.59/0.58  fof(f47,plain,(
% 1.59/0.58    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.59/0.58    inference(cnf_transformation,[],[f32])).
% 1.59/0.58  fof(f32,plain,(
% 1.59/0.58    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 1.59/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f31])).
% 1.59/0.58  fof(f31,plain,(
% 1.59/0.58    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.59/0.58    introduced(choice_axiom,[])).
% 1.59/0.58  fof(f18,plain,(
% 1.59/0.58    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.59/0.58    inference(ennf_transformation,[],[f3])).
% 1.59/0.58  fof(f3,axiom,(
% 1.59/0.58    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.59/0.58  fof(f282,plain,(
% 1.59/0.58    ( ! [X1] : (~r2_hidden(X1,sK1)) ) | ~spl6_6),
% 1.59/0.58    inference(resolution,[],[f280,f89])).
% 1.59/0.58  fof(f89,plain,(
% 1.59/0.58    ( ! [X4,X3] : (~r1_tarski(X4,k1_xboole_0) | ~r2_hidden(X3,X4)) )),
% 1.59/0.58    inference(resolution,[],[f84,f58])).
% 1.59/0.58  fof(f58,plain,(
% 1.59/0.58    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f39])).
% 1.59/0.58  fof(f39,plain,(
% 1.59/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.59/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).
% 1.59/0.58  fof(f38,plain,(
% 1.59/0.58    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.59/0.58    introduced(choice_axiom,[])).
% 1.59/0.58  fof(f37,plain,(
% 1.59/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.59/0.58    inference(rectify,[],[f36])).
% 1.59/0.58  fof(f36,plain,(
% 1.59/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.59/0.58    inference(nnf_transformation,[],[f25])).
% 1.59/0.58  fof(f25,plain,(
% 1.59/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.59/0.58    inference(ennf_transformation,[],[f1])).
% 1.59/0.58  fof(f1,axiom,(
% 1.59/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.59/0.58  fof(f84,plain,(
% 1.59/0.58    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 1.59/0.58    inference(condensation,[],[f83])).
% 1.59/0.58  fof(f83,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,X0)) )),
% 1.59/0.58    inference(trivial_inequality_removal,[],[f82])).
% 1.59/0.58  fof(f82,plain,(
% 1.59/0.58    ( ! [X0,X1] : (k1_xboole_0 != k1_xboole_0 | ~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,X0)) )),
% 1.59/0.58    inference(superposition,[],[f70,f46])).
% 1.59/0.58  fof(f46,plain,(
% 1.59/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f4])).
% 1.59/0.58  fof(f4,axiom,(
% 1.59/0.58    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 1.59/0.58  fof(f70,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(X2,X1) != X2 | ~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.59/0.58    inference(resolution,[],[f50,f57])).
% 1.59/0.58  fof(f57,plain,(
% 1.59/0.58    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 1.59/0.58    inference(cnf_transformation,[],[f35])).
% 1.59/0.58  fof(f35,plain,(
% 1.59/0.58    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.59/0.58    inference(nnf_transformation,[],[f5])).
% 1.59/0.58  fof(f5,axiom,(
% 1.59/0.58    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.59/0.58  fof(f50,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f34])).
% 1.59/0.58  fof(f34,plain,(
% 1.59/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.59/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f33])).
% 1.59/0.58  fof(f33,plain,(
% 1.59/0.58    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.59/0.58    introduced(choice_axiom,[])).
% 1.59/0.58  fof(f19,plain,(
% 1.59/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.59/0.58    inference(ennf_transformation,[],[f15])).
% 1.59/0.58  fof(f15,plain,(
% 1.59/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.59/0.58    inference(rectify,[],[f2])).
% 1.59/0.58  fof(f2,axiom,(
% 1.59/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.59/0.58  fof(f280,plain,(
% 1.59/0.58    r1_tarski(sK1,k1_xboole_0) | ~spl6_6),
% 1.59/0.58    inference(forward_demodulation,[],[f43,f234])).
% 1.59/0.58  fof(f234,plain,(
% 1.59/0.58    k1_xboole_0 = sK2 | ~spl6_6),
% 1.59/0.58    inference(avatar_component_clause,[],[f232])).
% 1.59/0.58  fof(f232,plain,(
% 1.59/0.58    spl6_6 <=> k1_xboole_0 = sK2),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.59/0.58  fof(f263,plain,(
% 1.59/0.58    ~spl6_4 | ~spl6_6),
% 1.59/0.58    inference(avatar_contradiction_clause,[],[f262])).
% 1.59/0.58  fof(f262,plain,(
% 1.59/0.58    $false | (~spl6_4 | ~spl6_6)),
% 1.59/0.58    inference(subsumption_resolution,[],[f261,f69])).
% 1.59/0.58  fof(f69,plain,(
% 1.59/0.58    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.59/0.58    inference(duplicate_literal_removal,[],[f68])).
% 1.59/0.58  fof(f68,plain,(
% 1.59/0.58    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 1.59/0.58    inference(resolution,[],[f60,f59])).
% 1.59/0.58  fof(f59,plain,(
% 1.59/0.58    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f39])).
% 1.59/0.58  fof(f60,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f39])).
% 1.59/0.58  fof(f261,plain,(
% 1.59/0.58    ~r1_tarski(sK0,sK0) | (~spl6_4 | ~spl6_6)),
% 1.59/0.58    inference(forward_demodulation,[],[f260,f78])).
% 1.59/0.58  fof(f260,plain,(
% 1.59/0.58    ~r1_tarski(k8_setfam_1(sK0,k1_xboole_0),sK0) | (~spl6_4 | ~spl6_6)),
% 1.59/0.58    inference(forward_demodulation,[],[f251,f234])).
% 1.59/0.58  fof(f251,plain,(
% 1.59/0.58    ~r1_tarski(k8_setfam_1(sK0,sK2),sK0) | ~spl6_4),
% 1.59/0.58    inference(forward_demodulation,[],[f243,f78])).
% 1.59/0.58  fof(f243,plain,(
% 1.59/0.58    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) | ~spl6_4),
% 1.59/0.58    inference(backward_demodulation,[],[f44,f225])).
% 1.59/0.58  fof(f239,plain,(
% 1.59/0.58    spl6_6 | spl6_7),
% 1.59/0.58    inference(avatar_split_clause,[],[f215,f236,f232])).
% 1.59/0.58  fof(f215,plain,(
% 1.59/0.58    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | k1_xboole_0 = sK2),
% 1.59/0.58    inference(resolution,[],[f152,f42])).
% 1.59/0.58  fof(f152,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k8_setfam_1(X0,X1) = k1_setfam_1(X1) | k1_xboole_0 = X1) )),
% 1.59/0.58    inference(duplicate_literal_removal,[],[f151])).
% 1.59/0.58  fof(f151,plain,(
% 1.59/0.58    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.59/0.58    inference(superposition,[],[f52,f54])).
% 1.59/0.58  fof(f54,plain,(
% 1.59/0.58    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.59/0.58    inference(cnf_transformation,[],[f24])).
% 1.59/0.58  fof(f52,plain,(
% 1.59/0.58    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.59/0.58    inference(cnf_transformation,[],[f22])).
% 1.59/0.58  fof(f22,plain,(
% 1.59/0.58    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.59/0.58    inference(ennf_transformation,[],[f9])).
% 1.59/0.58  fof(f9,axiom,(
% 1.59/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 1.59/0.58  fof(f230,plain,(
% 1.59/0.58    spl6_4 | spl6_5),
% 1.59/0.58    inference(avatar_split_clause,[],[f214,f227,f223])).
% 1.59/0.58  fof(f214,plain,(
% 1.59/0.58    k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | k1_xboole_0 = sK1),
% 1.59/0.58    inference(resolution,[],[f152,f41])).
% 1.59/0.58  fof(f41,plain,(
% 1.59/0.58    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.59/0.58    inference(cnf_transformation,[],[f30])).
% 1.59/0.58  % SZS output end Proof for theBenchmark
% 1.59/0.58  % (29848)------------------------------
% 1.59/0.58  % (29848)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (29848)Termination reason: Refutation
% 1.59/0.58  
% 1.59/0.58  % (29848)Memory used [KB]: 10874
% 1.59/0.58  % (29848)Time elapsed: 0.141 s
% 1.59/0.58  % (29848)------------------------------
% 1.59/0.58  % (29848)------------------------------
% 1.59/0.58  % (29844)Success in time 0.207 s
%------------------------------------------------------------------------------
