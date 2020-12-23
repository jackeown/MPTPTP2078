%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:13 EST 2020

% Result     : Theorem 3.59s
% Output     : Refutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :  198 ( 827 expanded)
%              Number of leaves         :   40 ( 259 expanded)
%              Depth                    :   17
%              Number of atoms          :  532 (2808 expanded)
%              Number of equality atoms :   63 ( 452 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5058,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f120,f123,f134,f141,f147,f279,f1411,f1553,f1784,f2267,f2305,f4499,f4828,f5052])).

fof(f5052,plain,
    ( ~ spl6_11
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_135
    | ~ spl6_240 ),
    inference(avatar_split_clause,[],[f5044,f4826,f2265,f139,f132,f118,f115,f267])).

fof(f267,plain,
    ( spl6_11
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f115,plain,
    ( spl6_1
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f118,plain,
    ( spl6_2
  <=> r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f132,plain,
    ( spl6_4
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f139,plain,
    ( spl6_5
  <=> r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f2265,plain,
    ( spl6_135
  <=> ! [X0] : ~ r2_hidden(X0,k5_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_135])])).

fof(f4826,plain,
    ( spl6_240
  <=> ! [X0] : ~ r2_hidden(X0,k5_xboole_0(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_240])])).

fof(f5044,plain,
    ( r1_tarski(sK1,sK2)
    | ~ r1_tarski(sK1,sK0)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_135
    | ~ spl6_240 ),
    inference(resolution,[],[f4993,f1562])).

fof(f1562,plain,
    ( r1_xboole_0(k5_xboole_0(sK0,sK2),sK1)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(resolution,[],[f1555,f416])).

fof(f416,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k5_xboole_0(sK0,sK1))
        | r1_xboole_0(X0,sK1) )
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f167,f398])).

fof(f398,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f125,f214])).

fof(f214,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl6_4 ),
    inference(superposition,[],[f154,f73])).

fof(f73,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f154,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl6_4 ),
    inference(resolution,[],[f148,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f148,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl6_4 ),
    inference(resolution,[],[f133,f113])).

fof(f113,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK5(X0,X1),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r1_tarski(sK5(X0,X1),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f57,f58])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK5(X0,X1),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( r1_tarski(sK5(X0,X1),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f133,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f132])).

fof(f125,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f60,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f87,f77])).

fof(f77,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f87,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f60,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | ~ r1_tarski(sK1,sK2) )
    & ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | r1_tarski(sK1,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f45,f47,f46])).

fof(f46,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | r1_tarski(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
            | ~ r1_tarski(sK1,X2) )
          & ( r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
            | r1_tarski(sK1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
          | ~ r1_tarski(sK1,X2) )
        & ( r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
          | r1_tarski(sK1,X2) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
        | ~ r1_tarski(sK1,sK2) )
      & ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
        | r1_tarski(sK1,sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(f167,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k3_subset_1(sK0,sK1))
      | r1_xboole_0(X0,sK1) ) ),
    inference(superposition,[],[f108,f125])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
      | r1_xboole_0(X0,X2) ) ),
    inference(definition_unfolding,[],[f94,f77])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f1555,plain,
    ( r1_tarski(k5_xboole_0(sK0,sK2),k5_xboole_0(sK0,sK1))
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f1554,f504])).

fof(f504,plain,
    ( k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2)
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f135,f328])).

fof(f328,plain,
    ( sK2 = k3_xboole_0(sK0,sK2)
    | ~ spl6_5 ),
    inference(superposition,[],[f162,f73])).

fof(f162,plain,
    ( sK2 = k3_xboole_0(sK2,sK0)
    | ~ spl6_5 ),
    inference(resolution,[],[f150,f86])).

fof(f150,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl6_5 ),
    inference(resolution,[],[f140,f113])).

fof(f140,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f139])).

fof(f135,plain,(
    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f61,f106])).

fof(f61,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f48])).

fof(f1554,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k5_xboole_0(sK0,sK1))
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f122,f398])).

fof(f122,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f118])).

fof(f4993,plain,
    ( ! [X2] :
        ( ~ r1_xboole_0(k5_xboole_0(sK0,sK2),X2)
        | r1_tarski(X2,sK2)
        | ~ r1_tarski(X2,sK0) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_135
    | ~ spl6_240 ),
    inference(resolution,[],[f4980,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f4980,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,k5_xboole_0(sK0,sK2))
        | ~ r1_tarski(X0,sK0)
        | r1_tarski(X0,sK2) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_135
    | ~ spl6_240 ),
    inference(backward_demodulation,[],[f652,f4896])).

fof(f4896,plain,
    ( sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK2))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_135
    | ~ spl6_240 ),
    inference(forward_demodulation,[],[f4878,f2609])).

fof(f2609,plain,
    ( sK0 = k5_xboole_0(sK0,k1_xboole_0)
    | ~ spl6_4
    | ~ spl6_135 ),
    inference(backward_demodulation,[],[f2362,f2608])).

fof(f2608,plain,
    ( sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1))
    | ~ spl6_4
    | ~ spl6_135 ),
    inference(forward_demodulation,[],[f2607,f100])).

fof(f100,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f66,f98])).

fof(f98,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f75,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f75,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f66,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f2607,plain,
    ( k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k3_tarski(k1_enumset1(sK0,sK0,k1_xboole_0))
    | ~ spl6_4
    | ~ spl6_135 ),
    inference(forward_demodulation,[],[f222,f2324])).

fof(f2324,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,sK1)
    | ~ spl6_135 ),
    inference(resolution,[],[f2306,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f2306,plain,
    ( v1_xboole_0(k5_xboole_0(sK1,sK1))
    | ~ spl6_135 ),
    inference(resolution,[],[f2266,f69])).

fof(f69,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f50,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f2266,plain,
    ( ! [X0] : ~ r2_hidden(X0,k5_xboole_0(sK1,sK1))
    | ~ spl6_135 ),
    inference(avatar_component_clause,[],[f2265])).

fof(f222,plain,
    ( k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k3_tarski(k1_enumset1(sK0,sK0,k5_xboole_0(sK1,sK1)))
    | ~ spl6_4 ),
    inference(superposition,[],[f105,f154])).

fof(f105,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f78,f98,f77,f98])).

fof(f78,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f2362,plain,
    ( k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0)
    | ~ spl6_4
    | ~ spl6_135 ),
    inference(backward_demodulation,[],[f221,f2324])).

fof(f221,plain,
    ( k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))
    | ~ spl6_4 ),
    inference(superposition,[],[f104,f154])).

fof(f104,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f76,f98,f77])).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f4878,plain,
    ( k3_tarski(k1_enumset1(sK0,sK0,sK2)) = k5_xboole_0(sK0,k1_xboole_0)
    | ~ spl6_5
    | ~ spl6_240 ),
    inference(backward_demodulation,[],[f335,f4865])).

fof(f4865,plain,
    ( k1_xboole_0 = k5_xboole_0(sK2,sK2)
    | ~ spl6_240 ),
    inference(resolution,[],[f4840,f67])).

fof(f4840,plain,
    ( v1_xboole_0(k5_xboole_0(sK2,sK2))
    | ~ spl6_240 ),
    inference(resolution,[],[f4827,f69])).

fof(f4827,plain,
    ( ! [X0] : ~ r2_hidden(X0,k5_xboole_0(sK2,sK2))
    | ~ spl6_240 ),
    inference(avatar_component_clause,[],[f4826])).

fof(f335,plain,
    ( k3_tarski(k1_enumset1(sK0,sK0,sK2)) = k5_xboole_0(sK0,k5_xboole_0(sK2,sK2))
    | ~ spl6_5 ),
    inference(superposition,[],[f104,f162])).

fof(f652,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k3_tarski(k1_enumset1(sK0,sK0,sK2)))
        | ~ r1_xboole_0(X0,k5_xboole_0(sK0,sK2))
        | r1_tarski(X0,sK2) )
    | ~ spl6_5 ),
    inference(superposition,[],[f111,f522])).

fof(f522,plain,
    ( k3_tarski(k1_enumset1(sK0,sK0,sK2)) = k3_tarski(k1_enumset1(sK2,sK2,k5_xboole_0(sK0,sK2)))
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f180,f504])).

fof(f180,plain,(
    k3_tarski(k1_enumset1(sK2,sK2,k3_subset_1(sK0,sK2))) = k3_tarski(k1_enumset1(sK0,sK0,sK2)) ),
    inference(forward_demodulation,[],[f175,f103])).

fof(f103,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f72,f74,f74])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f175,plain,(
    k3_tarski(k1_enumset1(sK2,sK2,sK0)) = k3_tarski(k1_enumset1(sK2,sK2,k3_subset_1(sK0,sK2))) ),
    inference(superposition,[],[f105,f135])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
      | ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f97,f98])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f4828,plain,
    ( ~ spl6_233
    | spl6_240
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f4811,f139,f4826,f4470])).

fof(f4470,plain,
    ( spl6_233
  <=> r1_xboole_0(k5_xboole_0(sK2,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_233])])).

fof(f4811,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k5_xboole_0(sK2,sK2))
        | ~ r1_xboole_0(k5_xboole_0(sK2,sK2),sK2) )
    | ~ spl6_5 ),
    inference(superposition,[],[f84,f635])).

fof(f635,plain,
    ( k5_xboole_0(sK2,sK2) = k3_xboole_0(k5_xboole_0(sK2,sK2),sK2)
    | ~ spl6_5 ),
    inference(resolution,[],[f334,f86])).

fof(f334,plain,
    ( r1_tarski(k5_xboole_0(sK2,sK2),sK2)
    | ~ spl6_5 ),
    inference(superposition,[],[f102,f162])).

fof(f102,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f71,f77])).

fof(f71,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f54])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f4499,plain,
    ( ~ spl6_5
    | spl6_233 ),
    inference(avatar_contradiction_clause,[],[f4496])).

fof(f4496,plain,
    ( $false
    | ~ spl6_5
    | spl6_233 ),
    inference(subsumption_resolution,[],[f709,f4475])).

fof(f4475,plain,
    ( ~ r1_xboole_0(sK2,k5_xboole_0(sK2,sK2))
    | spl6_233 ),
    inference(resolution,[],[f4471,f85])).

fof(f4471,plain,
    ( ~ r1_xboole_0(k5_xboole_0(sK2,sK2),sK2)
    | spl6_233 ),
    inference(avatar_component_clause,[],[f4470])).

fof(f709,plain,
    ( r1_xboole_0(sK2,k5_xboole_0(sK2,sK2))
    | ~ spl6_5 ),
    inference(superposition,[],[f160,f162])).

fof(f160,plain,
    ( ! [X0] : r1_xboole_0(sK2,k5_xboole_0(X0,k3_xboole_0(X0,sK0)))
    | ~ spl6_5 ),
    inference(resolution,[],[f150,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ) ),
    inference(definition_unfolding,[],[f92,f77])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f2305,plain,
    ( ~ spl6_4
    | spl6_134 ),
    inference(avatar_contradiction_clause,[],[f2302])).

fof(f2302,plain,
    ( $false
    | ~ spl6_4
    | spl6_134 ),
    inference(subsumption_resolution,[],[f703,f2294])).

fof(f2294,plain,
    ( ~ r1_xboole_0(sK1,k5_xboole_0(sK1,sK1))
    | spl6_134 ),
    inference(resolution,[],[f2263,f85])).

fof(f2263,plain,
    ( ~ r1_xboole_0(k5_xboole_0(sK1,sK1),sK1)
    | spl6_134 ),
    inference(avatar_component_clause,[],[f2262])).

fof(f2262,plain,
    ( spl6_134
  <=> r1_xboole_0(k5_xboole_0(sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_134])])).

fof(f703,plain,
    ( r1_xboole_0(sK1,k5_xboole_0(sK1,sK1))
    | ~ spl6_4 ),
    inference(superposition,[],[f152,f154])).

fof(f152,plain,
    ( ! [X0] : r1_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,sK0)))
    | ~ spl6_4 ),
    inference(resolution,[],[f148,f107])).

fof(f2267,plain,
    ( ~ spl6_134
    | spl6_135
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f2250,f132,f2265,f2262])).

fof(f2250,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k5_xboole_0(sK1,sK1))
        | ~ r1_xboole_0(k5_xboole_0(sK1,sK1),sK1) )
    | ~ spl6_4 ),
    inference(superposition,[],[f84,f476])).

fof(f476,plain,
    ( k5_xboole_0(sK1,sK1) = k3_xboole_0(k5_xboole_0(sK1,sK1),sK1)
    | ~ spl6_4 ),
    inference(resolution,[],[f220,f86])).

fof(f220,plain,
    ( r1_tarski(k5_xboole_0(sK1,sK1),sK1)
    | ~ spl6_4 ),
    inference(superposition,[],[f102,f154])).

fof(f1784,plain,
    ( ~ spl6_5
    | spl6_81 ),
    inference(avatar_contradiction_clause,[],[f1782])).

fof(f1782,plain,
    ( $false
    | ~ spl6_5
    | spl6_81 ),
    inference(subsumption_resolution,[],[f517,f1410])).

fof(f1410,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK0)
    | spl6_81 ),
    inference(avatar_component_clause,[],[f1409])).

fof(f1409,plain,
    ( spl6_81
  <=> r1_tarski(k5_xboole_0(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_81])])).

fof(f517,plain,
    ( r1_tarski(k5_xboole_0(sK0,sK2),sK0)
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f173,f504])).

fof(f173,plain,(
    r1_tarski(k3_subset_1(sK0,sK2),sK0) ),
    inference(superposition,[],[f102,f135])).

fof(f1553,plain,
    ( ~ spl6_1
    | ~ spl6_5
    | spl6_78 ),
    inference(avatar_contradiction_clause,[],[f1550])).

fof(f1550,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_5
    | spl6_78 ),
    inference(subsumption_resolution,[],[f1443,f1500])).

fof(f1500,plain,
    ( ~ r1_xboole_0(sK1,k5_xboole_0(sK0,sK2))
    | spl6_78 ),
    inference(resolution,[],[f1390,f85])).

fof(f1390,plain,
    ( ~ r1_xboole_0(k5_xboole_0(sK0,sK2),sK1)
    | spl6_78 ),
    inference(avatar_component_clause,[],[f1389])).

fof(f1389,plain,
    ( spl6_78
  <=> r1_xboole_0(k5_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f1443,plain,
    ( r1_xboole_0(sK1,k5_xboole_0(sK0,sK2))
    | ~ spl6_1
    | ~ spl6_5 ),
    inference(superposition,[],[f1428,f162])).

fof(f1428,plain,
    ( ! [X0] : r1_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(sK2,X0)))
    | ~ spl6_1 ),
    inference(superposition,[],[f1403,f73])).

fof(f1403,plain,
    ( ! [X0] : r1_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,sK2)))
    | ~ spl6_1 ),
    inference(resolution,[],[f121,f107])).

fof(f121,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f115])).

fof(f1411,plain,
    ( ~ spl6_81
    | ~ spl6_78
    | spl6_2
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f1406,f139,f132,f118,f1389,f1409])).

fof(f1406,plain,
    ( ~ r1_xboole_0(k5_xboole_0(sK0,sK2),sK1)
    | ~ r1_tarski(k5_xboole_0(sK0,sK2),sK0)
    | spl6_2
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(resolution,[],[f1402,f418])).

fof(f418,plain,
    ( ! [X2] :
        ( r1_tarski(X2,k5_xboole_0(sK0,sK1))
        | ~ r1_xboole_0(X2,sK1)
        | ~ r1_tarski(X2,sK0) )
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f169,f398])).

fof(f169,plain,(
    ! [X2] :
      ( r1_tarski(X2,k3_subset_1(sK0,sK1))
      | ~ r1_xboole_0(X2,sK1)
      | ~ r1_tarski(X2,sK0) ) ),
    inference(superposition,[],[f110,f125])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f95,f77])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f1402,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,sK2),k5_xboole_0(sK0,sK1))
    | spl6_2
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f1401,f504])).

fof(f1401,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k5_xboole_0(sK0,sK1))
    | spl6_2
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f119,f398])).

fof(f119,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f118])).

fof(f279,plain,
    ( ~ spl6_4
    | spl6_11 ),
    inference(avatar_contradiction_clause,[],[f277])).

fof(f277,plain,
    ( $false
    | ~ spl6_4
    | spl6_11 ),
    inference(subsumption_resolution,[],[f148,f268])).

fof(f268,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl6_11 ),
    inference(avatar_component_clause,[],[f267])).

fof(f147,plain,(
    ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | ~ spl6_3 ),
    inference(resolution,[],[f130,f64])).

fof(f64,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f130,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl6_3
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f141,plain,
    ( spl6_3
    | spl6_5 ),
    inference(avatar_split_clause,[],[f136,f139,f129])).

fof(f136,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f61,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f134,plain,
    ( spl6_3
    | spl6_4 ),
    inference(avatar_split_clause,[],[f126,f132,f129])).

fof(f126,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f60,f79])).

fof(f123,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f62,f118,f115])).

fof(f62,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f120,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f63,f118,f115])).

fof(f63,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:58:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (6039)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (6031)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (6023)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (6020)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (6017)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (6044)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (6021)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (6025)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (6019)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (6036)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (6018)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (6022)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (6040)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (6045)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (6043)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (6033)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (6032)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (6046)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (6030)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (6035)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (6037)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (6026)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.56  % (6024)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.56  % (6038)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  % (6041)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.56  % (6029)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (6028)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (6027)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.58  % (6034)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.60  % (6042)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 2.89/0.83  % (6022)Time limit reached!
% 2.89/0.83  % (6022)------------------------------
% 2.89/0.83  % (6022)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.89/0.83  % (6022)Termination reason: Time limit
% 2.89/0.83  
% 2.89/0.83  % (6022)Memory used [KB]: 8187
% 2.89/0.83  % (6022)Time elapsed: 0.413 s
% 2.89/0.83  % (6022)------------------------------
% 2.89/0.83  % (6022)------------------------------
% 3.59/0.87  % (6019)Refutation found. Thanks to Tanya!
% 3.59/0.87  % SZS status Theorem for theBenchmark
% 3.59/0.87  % SZS output start Proof for theBenchmark
% 3.59/0.87  fof(f5058,plain,(
% 3.59/0.87    $false),
% 3.59/0.87    inference(avatar_sat_refutation,[],[f120,f123,f134,f141,f147,f279,f1411,f1553,f1784,f2267,f2305,f4499,f4828,f5052])).
% 3.59/0.87  fof(f5052,plain,(
% 3.59/0.87    ~spl6_11 | spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_135 | ~spl6_240),
% 3.59/0.87    inference(avatar_split_clause,[],[f5044,f4826,f2265,f139,f132,f118,f115,f267])).
% 3.59/0.87  fof(f267,plain,(
% 3.59/0.87    spl6_11 <=> r1_tarski(sK1,sK0)),
% 3.59/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 3.59/0.87  fof(f115,plain,(
% 3.59/0.87    spl6_1 <=> r1_tarski(sK1,sK2)),
% 3.59/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 3.59/0.87  fof(f118,plain,(
% 3.59/0.87    spl6_2 <=> r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))),
% 3.59/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 3.59/0.87  fof(f132,plain,(
% 3.59/0.87    spl6_4 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 3.59/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 3.59/0.87  fof(f139,plain,(
% 3.59/0.87    spl6_5 <=> r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 3.59/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 3.59/0.87  fof(f2265,plain,(
% 3.59/0.87    spl6_135 <=> ! [X0] : ~r2_hidden(X0,k5_xboole_0(sK1,sK1))),
% 3.59/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_135])])).
% 3.59/0.87  fof(f4826,plain,(
% 3.59/0.87    spl6_240 <=> ! [X0] : ~r2_hidden(X0,k5_xboole_0(sK2,sK2))),
% 3.59/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_240])])).
% 3.59/0.87  fof(f5044,plain,(
% 3.59/0.87    r1_tarski(sK1,sK2) | ~r1_tarski(sK1,sK0) | (~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_135 | ~spl6_240)),
% 3.59/0.87    inference(resolution,[],[f4993,f1562])).
% 3.59/0.87  fof(f1562,plain,(
% 3.59/0.87    r1_xboole_0(k5_xboole_0(sK0,sK2),sK1) | (~spl6_2 | ~spl6_4 | ~spl6_5)),
% 3.59/0.87    inference(resolution,[],[f1555,f416])).
% 3.59/0.87  fof(f416,plain,(
% 3.59/0.87    ( ! [X0] : (~r1_tarski(X0,k5_xboole_0(sK0,sK1)) | r1_xboole_0(X0,sK1)) ) | ~spl6_4),
% 3.59/0.87    inference(backward_demodulation,[],[f167,f398])).
% 3.59/0.87  fof(f398,plain,(
% 3.59/0.87    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) | ~spl6_4),
% 3.59/0.87    inference(backward_demodulation,[],[f125,f214])).
% 3.59/0.87  fof(f214,plain,(
% 3.59/0.87    sK1 = k3_xboole_0(sK0,sK1) | ~spl6_4),
% 3.59/0.87    inference(superposition,[],[f154,f73])).
% 3.59/0.87  fof(f73,plain,(
% 3.59/0.87    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.59/0.87    inference(cnf_transformation,[],[f1])).
% 3.59/0.87  fof(f1,axiom,(
% 3.59/0.87    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.59/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.59/0.87  fof(f154,plain,(
% 3.59/0.87    sK1 = k3_xboole_0(sK1,sK0) | ~spl6_4),
% 3.59/0.87    inference(resolution,[],[f148,f86])).
% 3.59/0.87  fof(f86,plain,(
% 3.59/0.87    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 3.59/0.87    inference(cnf_transformation,[],[f34])).
% 3.59/0.87  fof(f34,plain,(
% 3.59/0.87    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.59/0.87    inference(ennf_transformation,[],[f10])).
% 3.59/0.87  fof(f10,axiom,(
% 3.59/0.87    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.59/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 3.59/0.87  fof(f148,plain,(
% 3.59/0.87    r1_tarski(sK1,sK0) | ~spl6_4),
% 3.59/0.87    inference(resolution,[],[f133,f113])).
% 3.59/0.87  fof(f113,plain,(
% 3.59/0.87    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 3.59/0.87    inference(equality_resolution,[],[f88])).
% 3.59/0.87  fof(f88,plain,(
% 3.59/0.87    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.59/0.87    inference(cnf_transformation,[],[f59])).
% 3.59/0.87  fof(f59,plain,(
% 3.59/0.87    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK5(X0,X1),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r1_tarski(sK5(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.59/0.87    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f57,f58])).
% 3.59/0.87  fof(f58,plain,(
% 3.59/0.87    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK5(X0,X1),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r1_tarski(sK5(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 3.59/0.87    introduced(choice_axiom,[])).
% 3.59/0.87  fof(f57,plain,(
% 3.59/0.87    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.59/0.87    inference(rectify,[],[f56])).
% 3.59/0.87  fof(f56,plain,(
% 3.59/0.87    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.59/0.87    inference(nnf_transformation,[],[f21])).
% 3.59/0.87  fof(f21,axiom,(
% 3.59/0.87    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.59/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 3.59/0.87  fof(f133,plain,(
% 3.59/0.87    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl6_4),
% 3.59/0.87    inference(avatar_component_clause,[],[f132])).
% 3.59/0.87  fof(f125,plain,(
% 3.59/0.87    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 3.59/0.87    inference(resolution,[],[f60,f106])).
% 3.59/0.87  fof(f106,plain,(
% 3.59/0.87    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 3.59/0.87    inference(definition_unfolding,[],[f87,f77])).
% 3.59/0.87  fof(f77,plain,(
% 3.59/0.87    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.59/0.87    inference(cnf_transformation,[],[f6])).
% 3.59/0.87  fof(f6,axiom,(
% 3.59/0.87    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.59/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 3.59/0.87  fof(f87,plain,(
% 3.59/0.87    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.59/0.87    inference(cnf_transformation,[],[f35])).
% 3.59/0.87  fof(f35,plain,(
% 3.59/0.87    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.59/0.87    inference(ennf_transformation,[],[f24])).
% 3.59/0.87  fof(f24,axiom,(
% 3.59/0.87    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.59/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 3.59/0.87  fof(f60,plain,(
% 3.59/0.87    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 3.59/0.87    inference(cnf_transformation,[],[f48])).
% 3.59/0.87  fof(f48,plain,(
% 3.59/0.87    ((~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)) & (r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 3.59/0.87    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f45,f47,f46])).
% 3.59/0.87  fof(f46,plain,(
% 3.59/0.87    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,X2)) & (r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 3.59/0.87    introduced(choice_axiom,[])).
% 3.59/0.87  fof(f47,plain,(
% 3.59/0.87    ? [X2] : ((~r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,X2)) & (r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => ((~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)) & (r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 3.59/0.87    introduced(choice_axiom,[])).
% 3.59/0.87  fof(f45,plain,(
% 3.59/0.87    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.59/0.87    inference(flattening,[],[f44])).
% 3.59/0.87  fof(f44,plain,(
% 3.59/0.87    ? [X0,X1] : (? [X2] : (((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.59/0.87    inference(nnf_transformation,[],[f29])).
% 3.59/0.87  fof(f29,plain,(
% 3.59/0.87    ? [X0,X1] : (? [X2] : ((r1_tarski(X1,X2) <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.59/0.87    inference(ennf_transformation,[],[f27])).
% 3.59/0.87  fof(f27,negated_conjecture,(
% 3.59/0.87    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 3.59/0.87    inference(negated_conjecture,[],[f26])).
% 3.59/0.87  fof(f26,conjecture,(
% 3.59/0.87    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 3.59/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).
% 3.59/0.87  fof(f167,plain,(
% 3.59/0.87    ( ! [X0] : (~r1_tarski(X0,k3_subset_1(sK0,sK1)) | r1_xboole_0(X0,sK1)) )),
% 3.59/0.87    inference(superposition,[],[f108,f125])).
% 3.59/0.87  fof(f108,plain,(
% 3.59/0.87    ( ! [X2,X0,X1] : (~r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) | r1_xboole_0(X0,X2)) )),
% 3.59/0.87    inference(definition_unfolding,[],[f94,f77])).
% 3.59/0.87  fof(f94,plain,(
% 3.59/0.87    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 3.59/0.87    inference(cnf_transformation,[],[f37])).
% 3.59/0.87  fof(f37,plain,(
% 3.59/0.87    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 3.59/0.87    inference(ennf_transformation,[],[f7])).
% 3.59/0.87  fof(f7,axiom,(
% 3.59/0.87    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 3.59/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 3.59/0.87  fof(f1555,plain,(
% 3.59/0.87    r1_tarski(k5_xboole_0(sK0,sK2),k5_xboole_0(sK0,sK1)) | (~spl6_2 | ~spl6_4 | ~spl6_5)),
% 3.59/0.87    inference(forward_demodulation,[],[f1554,f504])).
% 3.59/0.87  fof(f504,plain,(
% 3.59/0.87    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) | ~spl6_5),
% 3.59/0.87    inference(backward_demodulation,[],[f135,f328])).
% 3.59/0.87  fof(f328,plain,(
% 3.59/0.87    sK2 = k3_xboole_0(sK0,sK2) | ~spl6_5),
% 3.59/0.87    inference(superposition,[],[f162,f73])).
% 3.59/0.87  fof(f162,plain,(
% 3.59/0.87    sK2 = k3_xboole_0(sK2,sK0) | ~spl6_5),
% 3.59/0.87    inference(resolution,[],[f150,f86])).
% 3.59/0.87  fof(f150,plain,(
% 3.59/0.87    r1_tarski(sK2,sK0) | ~spl6_5),
% 3.59/0.87    inference(resolution,[],[f140,f113])).
% 3.59/0.87  fof(f140,plain,(
% 3.59/0.87    r2_hidden(sK2,k1_zfmisc_1(sK0)) | ~spl6_5),
% 3.59/0.87    inference(avatar_component_clause,[],[f139])).
% 3.59/0.87  fof(f135,plain,(
% 3.59/0.87    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 3.59/0.87    inference(resolution,[],[f61,f106])).
% 3.59/0.87  fof(f61,plain,(
% 3.59/0.87    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 3.59/0.87    inference(cnf_transformation,[],[f48])).
% 3.59/0.87  fof(f1554,plain,(
% 3.59/0.87    r1_tarski(k3_subset_1(sK0,sK2),k5_xboole_0(sK0,sK1)) | (~spl6_2 | ~spl6_4)),
% 3.59/0.87    inference(forward_demodulation,[],[f122,f398])).
% 3.59/0.87  fof(f122,plain,(
% 3.59/0.87    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~spl6_2),
% 3.59/0.87    inference(avatar_component_clause,[],[f118])).
% 3.59/0.87  fof(f4993,plain,(
% 3.59/0.87    ( ! [X2] : (~r1_xboole_0(k5_xboole_0(sK0,sK2),X2) | r1_tarski(X2,sK2) | ~r1_tarski(X2,sK0)) ) | (~spl6_4 | ~spl6_5 | ~spl6_135 | ~spl6_240)),
% 3.59/0.87    inference(resolution,[],[f4980,f85])).
% 3.59/0.87  fof(f85,plain,(
% 3.59/0.87    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 3.59/0.87    inference(cnf_transformation,[],[f33])).
% 3.59/0.87  fof(f33,plain,(
% 3.59/0.87    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.59/0.87    inference(ennf_transformation,[],[f4])).
% 3.59/0.87  fof(f4,axiom,(
% 3.59/0.87    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 3.59/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 3.59/0.87  fof(f4980,plain,(
% 3.59/0.87    ( ! [X0] : (~r1_xboole_0(X0,k5_xboole_0(sK0,sK2)) | ~r1_tarski(X0,sK0) | r1_tarski(X0,sK2)) ) | (~spl6_4 | ~spl6_5 | ~spl6_135 | ~spl6_240)),
% 3.59/0.87    inference(backward_demodulation,[],[f652,f4896])).
% 3.59/0.87  fof(f4896,plain,(
% 3.59/0.87    sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK2)) | (~spl6_4 | ~spl6_5 | ~spl6_135 | ~spl6_240)),
% 3.59/0.87    inference(forward_demodulation,[],[f4878,f2609])).
% 3.59/0.87  fof(f2609,plain,(
% 3.59/0.87    sK0 = k5_xboole_0(sK0,k1_xboole_0) | (~spl6_4 | ~spl6_135)),
% 3.59/0.87    inference(backward_demodulation,[],[f2362,f2608])).
% 3.59/0.87  fof(f2608,plain,(
% 3.59/0.87    sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) | (~spl6_4 | ~spl6_135)),
% 3.59/0.87    inference(forward_demodulation,[],[f2607,f100])).
% 3.59/0.87  fof(f100,plain,(
% 3.59/0.87    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0) )),
% 3.59/0.87    inference(definition_unfolding,[],[f66,f98])).
% 3.59/0.87  fof(f98,plain,(
% 3.59/0.87    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 3.59/0.87    inference(definition_unfolding,[],[f75,f74])).
% 3.59/0.87  fof(f74,plain,(
% 3.59/0.87    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.59/0.87    inference(cnf_transformation,[],[f20])).
% 3.59/0.87  fof(f20,axiom,(
% 3.59/0.87    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.59/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 3.59/0.87  fof(f75,plain,(
% 3.59/0.87    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.59/0.87    inference(cnf_transformation,[],[f22])).
% 3.59/0.87  fof(f22,axiom,(
% 3.59/0.87    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.59/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 3.59/0.87  fof(f66,plain,(
% 3.59/0.87    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.59/0.87    inference(cnf_transformation,[],[f8])).
% 3.59/0.87  fof(f8,axiom,(
% 3.59/0.87    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.59/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 3.59/0.87  fof(f2607,plain,(
% 3.59/0.87    k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k3_tarski(k1_enumset1(sK0,sK0,k1_xboole_0)) | (~spl6_4 | ~spl6_135)),
% 3.59/0.87    inference(forward_demodulation,[],[f222,f2324])).
% 3.59/0.87  fof(f2324,plain,(
% 3.59/0.87    k1_xboole_0 = k5_xboole_0(sK1,sK1) | ~spl6_135),
% 3.59/0.87    inference(resolution,[],[f2306,f67])).
% 3.59/0.87  fof(f67,plain,(
% 3.59/0.87    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 3.59/0.87    inference(cnf_transformation,[],[f30])).
% 3.59/0.87  fof(f30,plain,(
% 3.59/0.87    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.59/0.87    inference(ennf_transformation,[],[f3])).
% 3.59/0.87  fof(f3,axiom,(
% 3.59/0.87    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.59/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 3.59/0.87  fof(f2306,plain,(
% 3.59/0.87    v1_xboole_0(k5_xboole_0(sK1,sK1)) | ~spl6_135),
% 3.59/0.87    inference(resolution,[],[f2266,f69])).
% 3.59/0.87  fof(f69,plain,(
% 3.59/0.87    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 3.59/0.87    inference(cnf_transformation,[],[f52])).
% 3.59/0.87  fof(f52,plain,(
% 3.59/0.87    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.59/0.87    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f50,f51])).
% 3.59/0.87  fof(f51,plain,(
% 3.59/0.87    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 3.59/0.87    introduced(choice_axiom,[])).
% 3.59/0.87  fof(f50,plain,(
% 3.59/0.87    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.59/0.87    inference(rectify,[],[f49])).
% 3.59/0.87  fof(f49,plain,(
% 3.59/0.87    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.59/0.87    inference(nnf_transformation,[],[f2])).
% 3.59/0.87  fof(f2,axiom,(
% 3.59/0.87    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.59/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 3.59/0.87  fof(f2266,plain,(
% 3.59/0.87    ( ! [X0] : (~r2_hidden(X0,k5_xboole_0(sK1,sK1))) ) | ~spl6_135),
% 3.59/0.87    inference(avatar_component_clause,[],[f2265])).
% 3.59/0.87  fof(f222,plain,(
% 3.59/0.87    k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k3_tarski(k1_enumset1(sK0,sK0,k5_xboole_0(sK1,sK1))) | ~spl6_4),
% 3.59/0.87    inference(superposition,[],[f105,f154])).
% 3.59/0.87  fof(f105,plain,(
% 3.59/0.87    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 3.59/0.87    inference(definition_unfolding,[],[f78,f98,f77,f98])).
% 3.59/0.87  fof(f78,plain,(
% 3.59/0.87    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.59/0.87    inference(cnf_transformation,[],[f12])).
% 3.59/0.87  fof(f12,axiom,(
% 3.59/0.87    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.59/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 3.59/0.87  fof(f2362,plain,(
% 3.59/0.87    k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0) | (~spl6_4 | ~spl6_135)),
% 3.59/0.87    inference(backward_demodulation,[],[f221,f2324])).
% 3.59/0.87  fof(f221,plain,(
% 3.59/0.87    k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) | ~spl6_4),
% 3.59/0.87    inference(superposition,[],[f104,f154])).
% 3.59/0.87  fof(f104,plain,(
% 3.59/0.87    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 3.59/0.87    inference(definition_unfolding,[],[f76,f98,f77])).
% 3.59/0.87  fof(f76,plain,(
% 3.59/0.87    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.59/0.87    inference(cnf_transformation,[],[f18])).
% 3.59/0.87  fof(f18,axiom,(
% 3.59/0.87    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.59/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 3.59/0.87  fof(f4878,plain,(
% 3.59/0.87    k3_tarski(k1_enumset1(sK0,sK0,sK2)) = k5_xboole_0(sK0,k1_xboole_0) | (~spl6_5 | ~spl6_240)),
% 3.59/0.87    inference(backward_demodulation,[],[f335,f4865])).
% 3.59/0.87  fof(f4865,plain,(
% 3.59/0.87    k1_xboole_0 = k5_xboole_0(sK2,sK2) | ~spl6_240),
% 3.59/0.87    inference(resolution,[],[f4840,f67])).
% 3.59/0.87  fof(f4840,plain,(
% 3.59/0.87    v1_xboole_0(k5_xboole_0(sK2,sK2)) | ~spl6_240),
% 3.59/0.87    inference(resolution,[],[f4827,f69])).
% 3.59/0.87  fof(f4827,plain,(
% 3.59/0.87    ( ! [X0] : (~r2_hidden(X0,k5_xboole_0(sK2,sK2))) ) | ~spl6_240),
% 3.59/0.87    inference(avatar_component_clause,[],[f4826])).
% 3.59/0.87  fof(f335,plain,(
% 3.59/0.87    k3_tarski(k1_enumset1(sK0,sK0,sK2)) = k5_xboole_0(sK0,k5_xboole_0(sK2,sK2)) | ~spl6_5),
% 3.59/0.87    inference(superposition,[],[f104,f162])).
% 3.59/0.87  fof(f652,plain,(
% 3.59/0.87    ( ! [X0] : (~r1_tarski(X0,k3_tarski(k1_enumset1(sK0,sK0,sK2))) | ~r1_xboole_0(X0,k5_xboole_0(sK0,sK2)) | r1_tarski(X0,sK2)) ) | ~spl6_5),
% 3.59/0.87    inference(superposition,[],[f111,f522])).
% 3.59/0.87  fof(f522,plain,(
% 3.59/0.87    k3_tarski(k1_enumset1(sK0,sK0,sK2)) = k3_tarski(k1_enumset1(sK2,sK2,k5_xboole_0(sK0,sK2))) | ~spl6_5),
% 3.59/0.87    inference(backward_demodulation,[],[f180,f504])).
% 3.59/0.87  fof(f180,plain,(
% 3.59/0.87    k3_tarski(k1_enumset1(sK2,sK2,k3_subset_1(sK0,sK2))) = k3_tarski(k1_enumset1(sK0,sK0,sK2))),
% 3.59/0.87    inference(forward_demodulation,[],[f175,f103])).
% 3.59/0.87  fof(f103,plain,(
% 3.59/0.87    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 3.59/0.87    inference(definition_unfolding,[],[f72,f74,f74])).
% 3.59/0.87  fof(f72,plain,(
% 3.59/0.87    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.59/0.87    inference(cnf_transformation,[],[f19])).
% 3.59/0.87  fof(f19,axiom,(
% 3.59/0.87    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.59/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 3.59/0.87  fof(f175,plain,(
% 3.59/0.87    k3_tarski(k1_enumset1(sK2,sK2,sK0)) = k3_tarski(k1_enumset1(sK2,sK2,k3_subset_1(sK0,sK2)))),
% 3.59/0.87    inference(superposition,[],[f105,f135])).
% 3.59/0.87  fof(f111,plain,(
% 3.59/0.87    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) | ~r1_xboole_0(X0,X2) | r1_tarski(X0,X1)) )),
% 3.59/0.87    inference(definition_unfolding,[],[f97,f98])).
% 3.59/0.87  fof(f97,plain,(
% 3.59/0.87    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 3.59/0.87    inference(cnf_transformation,[],[f43])).
% 3.59/0.87  fof(f43,plain,(
% 3.59/0.87    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.59/0.87    inference(flattening,[],[f42])).
% 3.59/0.87  fof(f42,plain,(
% 3.59/0.87    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 3.59/0.87    inference(ennf_transformation,[],[f14])).
% 3.59/0.87  fof(f14,axiom,(
% 3.59/0.87    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 3.59/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).
% 3.59/0.87  fof(f4828,plain,(
% 3.59/0.87    ~spl6_233 | spl6_240 | ~spl6_5),
% 3.59/0.87    inference(avatar_split_clause,[],[f4811,f139,f4826,f4470])).
% 3.59/0.87  fof(f4470,plain,(
% 3.59/0.87    spl6_233 <=> r1_xboole_0(k5_xboole_0(sK2,sK2),sK2)),
% 3.59/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_233])])).
% 3.59/0.87  fof(f4811,plain,(
% 3.59/0.87    ( ! [X0] : (~r2_hidden(X0,k5_xboole_0(sK2,sK2)) | ~r1_xboole_0(k5_xboole_0(sK2,sK2),sK2)) ) | ~spl6_5),
% 3.59/0.87    inference(superposition,[],[f84,f635])).
% 3.59/0.87  fof(f635,plain,(
% 3.59/0.87    k5_xboole_0(sK2,sK2) = k3_xboole_0(k5_xboole_0(sK2,sK2),sK2) | ~spl6_5),
% 3.59/0.87    inference(resolution,[],[f334,f86])).
% 3.59/0.87  fof(f334,plain,(
% 3.59/0.87    r1_tarski(k5_xboole_0(sK2,sK2),sK2) | ~spl6_5),
% 3.59/0.87    inference(superposition,[],[f102,f162])).
% 3.59/0.87  fof(f102,plain,(
% 3.59/0.87    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 3.59/0.87    inference(definition_unfolding,[],[f71,f77])).
% 3.59/0.87  fof(f71,plain,(
% 3.59/0.87    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.59/0.87    inference(cnf_transformation,[],[f11])).
% 3.59/0.87  fof(f11,axiom,(
% 3.59/0.87    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.59/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 3.59/0.87  fof(f84,plain,(
% 3.59/0.87    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 3.59/0.87    inference(cnf_transformation,[],[f55])).
% 3.59/0.87  fof(f55,plain,(
% 3.59/0.87    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.59/0.87    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f54])).
% 3.59/0.87  fof(f54,plain,(
% 3.59/0.87    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 3.59/0.87    introduced(choice_axiom,[])).
% 3.59/0.87  fof(f32,plain,(
% 3.59/0.87    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.59/0.87    inference(ennf_transformation,[],[f28])).
% 3.59/0.87  fof(f28,plain,(
% 3.59/0.87    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.59/0.87    inference(rectify,[],[f5])).
% 3.59/0.87  fof(f5,axiom,(
% 3.59/0.87    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.59/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 3.59/0.87  fof(f4499,plain,(
% 3.59/0.87    ~spl6_5 | spl6_233),
% 3.59/0.87    inference(avatar_contradiction_clause,[],[f4496])).
% 3.59/0.87  fof(f4496,plain,(
% 3.59/0.87    $false | (~spl6_5 | spl6_233)),
% 3.59/0.87    inference(subsumption_resolution,[],[f709,f4475])).
% 3.59/0.87  fof(f4475,plain,(
% 3.59/0.87    ~r1_xboole_0(sK2,k5_xboole_0(sK2,sK2)) | spl6_233),
% 3.59/0.87    inference(resolution,[],[f4471,f85])).
% 3.59/0.87  fof(f4471,plain,(
% 3.59/0.87    ~r1_xboole_0(k5_xboole_0(sK2,sK2),sK2) | spl6_233),
% 3.59/0.87    inference(avatar_component_clause,[],[f4470])).
% 3.59/0.87  fof(f709,plain,(
% 3.59/0.87    r1_xboole_0(sK2,k5_xboole_0(sK2,sK2)) | ~spl6_5),
% 3.59/0.87    inference(superposition,[],[f160,f162])).
% 3.59/0.87  fof(f160,plain,(
% 3.59/0.87    ( ! [X0] : (r1_xboole_0(sK2,k5_xboole_0(X0,k3_xboole_0(X0,sK0)))) ) | ~spl6_5),
% 3.59/0.87    inference(resolution,[],[f150,f107])).
% 3.59/0.87  fof(f107,plain,(
% 3.59/0.87    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) )),
% 3.59/0.87    inference(definition_unfolding,[],[f92,f77])).
% 3.59/0.87  fof(f92,plain,(
% 3.59/0.87    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 3.59/0.87    inference(cnf_transformation,[],[f36])).
% 3.59/0.87  fof(f36,plain,(
% 3.59/0.87    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 3.59/0.87    inference(ennf_transformation,[],[f16])).
% 3.59/0.87  fof(f16,axiom,(
% 3.59/0.87    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 3.59/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 3.59/0.87  fof(f2305,plain,(
% 3.59/0.87    ~spl6_4 | spl6_134),
% 3.59/0.87    inference(avatar_contradiction_clause,[],[f2302])).
% 3.59/0.87  fof(f2302,plain,(
% 3.59/0.87    $false | (~spl6_4 | spl6_134)),
% 3.59/0.87    inference(subsumption_resolution,[],[f703,f2294])).
% 3.59/0.87  fof(f2294,plain,(
% 3.59/0.87    ~r1_xboole_0(sK1,k5_xboole_0(sK1,sK1)) | spl6_134),
% 3.59/0.87    inference(resolution,[],[f2263,f85])).
% 3.59/0.87  fof(f2263,plain,(
% 3.59/0.87    ~r1_xboole_0(k5_xboole_0(sK1,sK1),sK1) | spl6_134),
% 3.59/0.87    inference(avatar_component_clause,[],[f2262])).
% 3.59/0.87  fof(f2262,plain,(
% 3.59/0.87    spl6_134 <=> r1_xboole_0(k5_xboole_0(sK1,sK1),sK1)),
% 3.59/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_134])])).
% 3.59/0.87  fof(f703,plain,(
% 3.59/0.87    r1_xboole_0(sK1,k5_xboole_0(sK1,sK1)) | ~spl6_4),
% 3.59/0.87    inference(superposition,[],[f152,f154])).
% 3.59/0.87  fof(f152,plain,(
% 3.59/0.87    ( ! [X0] : (r1_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,sK0)))) ) | ~spl6_4),
% 3.59/0.87    inference(resolution,[],[f148,f107])).
% 3.59/0.87  fof(f2267,plain,(
% 3.59/0.87    ~spl6_134 | spl6_135 | ~spl6_4),
% 3.59/0.87    inference(avatar_split_clause,[],[f2250,f132,f2265,f2262])).
% 3.59/0.87  fof(f2250,plain,(
% 3.59/0.87    ( ! [X0] : (~r2_hidden(X0,k5_xboole_0(sK1,sK1)) | ~r1_xboole_0(k5_xboole_0(sK1,sK1),sK1)) ) | ~spl6_4),
% 3.59/0.87    inference(superposition,[],[f84,f476])).
% 3.59/0.87  fof(f476,plain,(
% 3.59/0.87    k5_xboole_0(sK1,sK1) = k3_xboole_0(k5_xboole_0(sK1,sK1),sK1) | ~spl6_4),
% 3.59/0.87    inference(resolution,[],[f220,f86])).
% 3.59/0.87  fof(f220,plain,(
% 3.59/0.87    r1_tarski(k5_xboole_0(sK1,sK1),sK1) | ~spl6_4),
% 3.59/0.87    inference(superposition,[],[f102,f154])).
% 3.59/0.87  fof(f1784,plain,(
% 3.59/0.87    ~spl6_5 | spl6_81),
% 3.59/0.87    inference(avatar_contradiction_clause,[],[f1782])).
% 3.59/0.87  fof(f1782,plain,(
% 3.59/0.87    $false | (~spl6_5 | spl6_81)),
% 3.59/0.87    inference(subsumption_resolution,[],[f517,f1410])).
% 3.59/0.87  fof(f1410,plain,(
% 3.59/0.87    ~r1_tarski(k5_xboole_0(sK0,sK2),sK0) | spl6_81),
% 3.59/0.87    inference(avatar_component_clause,[],[f1409])).
% 3.59/0.87  fof(f1409,plain,(
% 3.59/0.87    spl6_81 <=> r1_tarski(k5_xboole_0(sK0,sK2),sK0)),
% 3.59/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_81])])).
% 3.59/0.87  fof(f517,plain,(
% 3.59/0.87    r1_tarski(k5_xboole_0(sK0,sK2),sK0) | ~spl6_5),
% 3.59/0.87    inference(backward_demodulation,[],[f173,f504])).
% 3.59/0.87  fof(f173,plain,(
% 3.59/0.87    r1_tarski(k3_subset_1(sK0,sK2),sK0)),
% 3.59/0.87    inference(superposition,[],[f102,f135])).
% 3.59/0.87  fof(f1553,plain,(
% 3.59/0.87    ~spl6_1 | ~spl6_5 | spl6_78),
% 3.59/0.87    inference(avatar_contradiction_clause,[],[f1550])).
% 3.59/0.87  fof(f1550,plain,(
% 3.59/0.87    $false | (~spl6_1 | ~spl6_5 | spl6_78)),
% 3.59/0.87    inference(subsumption_resolution,[],[f1443,f1500])).
% 3.59/0.87  fof(f1500,plain,(
% 3.59/0.87    ~r1_xboole_0(sK1,k5_xboole_0(sK0,sK2)) | spl6_78),
% 3.59/0.87    inference(resolution,[],[f1390,f85])).
% 3.59/0.87  fof(f1390,plain,(
% 3.59/0.87    ~r1_xboole_0(k5_xboole_0(sK0,sK2),sK1) | spl6_78),
% 3.59/0.87    inference(avatar_component_clause,[],[f1389])).
% 3.59/0.87  fof(f1389,plain,(
% 3.59/0.87    spl6_78 <=> r1_xboole_0(k5_xboole_0(sK0,sK2),sK1)),
% 3.59/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).
% 3.59/0.87  fof(f1443,plain,(
% 3.59/0.87    r1_xboole_0(sK1,k5_xboole_0(sK0,sK2)) | (~spl6_1 | ~spl6_5)),
% 3.59/0.87    inference(superposition,[],[f1428,f162])).
% 3.59/0.87  fof(f1428,plain,(
% 3.59/0.87    ( ! [X0] : (r1_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(sK2,X0)))) ) | ~spl6_1),
% 3.59/0.87    inference(superposition,[],[f1403,f73])).
% 3.59/0.87  fof(f1403,plain,(
% 3.59/0.87    ( ! [X0] : (r1_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,sK2)))) ) | ~spl6_1),
% 3.59/0.87    inference(resolution,[],[f121,f107])).
% 3.59/0.87  fof(f121,plain,(
% 3.59/0.87    r1_tarski(sK1,sK2) | ~spl6_1),
% 3.59/0.87    inference(avatar_component_clause,[],[f115])).
% 3.59/0.87  fof(f1411,plain,(
% 3.59/0.87    ~spl6_81 | ~spl6_78 | spl6_2 | ~spl6_4 | ~spl6_5),
% 3.59/0.87    inference(avatar_split_clause,[],[f1406,f139,f132,f118,f1389,f1409])).
% 3.59/0.87  fof(f1406,plain,(
% 3.59/0.87    ~r1_xboole_0(k5_xboole_0(sK0,sK2),sK1) | ~r1_tarski(k5_xboole_0(sK0,sK2),sK0) | (spl6_2 | ~spl6_4 | ~spl6_5)),
% 3.59/0.87    inference(resolution,[],[f1402,f418])).
% 3.59/0.87  fof(f418,plain,(
% 3.59/0.87    ( ! [X2] : (r1_tarski(X2,k5_xboole_0(sK0,sK1)) | ~r1_xboole_0(X2,sK1) | ~r1_tarski(X2,sK0)) ) | ~spl6_4),
% 3.59/0.87    inference(backward_demodulation,[],[f169,f398])).
% 3.59/0.87  fof(f169,plain,(
% 3.59/0.87    ( ! [X2] : (r1_tarski(X2,k3_subset_1(sK0,sK1)) | ~r1_xboole_0(X2,sK1) | ~r1_tarski(X2,sK0)) )),
% 3.59/0.87    inference(superposition,[],[f110,f125])).
% 3.59/0.87  fof(f110,plain,(
% 3.59/0.87    ( ! [X2,X0,X1] : (r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.59/0.87    inference(definition_unfolding,[],[f95,f77])).
% 3.59/0.87  fof(f95,plain,(
% 3.59/0.87    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.59/0.87    inference(cnf_transformation,[],[f39])).
% 3.59/0.87  fof(f39,plain,(
% 3.59/0.87    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 3.59/0.87    inference(flattening,[],[f38])).
% 3.59/0.87  fof(f38,plain,(
% 3.59/0.87    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 3.59/0.87    inference(ennf_transformation,[],[f17])).
% 3.59/0.87  fof(f17,axiom,(
% 3.59/0.87    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 3.59/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).
% 3.59/0.87  fof(f1402,plain,(
% 3.59/0.87    ~r1_tarski(k5_xboole_0(sK0,sK2),k5_xboole_0(sK0,sK1)) | (spl6_2 | ~spl6_4 | ~spl6_5)),
% 3.59/0.87    inference(forward_demodulation,[],[f1401,f504])).
% 3.59/0.87  fof(f1401,plain,(
% 3.59/0.87    ~r1_tarski(k3_subset_1(sK0,sK2),k5_xboole_0(sK0,sK1)) | (spl6_2 | ~spl6_4)),
% 3.59/0.87    inference(forward_demodulation,[],[f119,f398])).
% 3.59/0.87  fof(f119,plain,(
% 3.59/0.87    ~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | spl6_2),
% 3.59/0.87    inference(avatar_component_clause,[],[f118])).
% 3.59/0.87  fof(f279,plain,(
% 3.59/0.87    ~spl6_4 | spl6_11),
% 3.59/0.87    inference(avatar_contradiction_clause,[],[f277])).
% 3.59/0.87  fof(f277,plain,(
% 3.59/0.87    $false | (~spl6_4 | spl6_11)),
% 3.59/0.87    inference(subsumption_resolution,[],[f148,f268])).
% 3.59/0.87  fof(f268,plain,(
% 3.59/0.87    ~r1_tarski(sK1,sK0) | spl6_11),
% 3.59/0.87    inference(avatar_component_clause,[],[f267])).
% 3.59/0.87  fof(f147,plain,(
% 3.59/0.87    ~spl6_3),
% 3.59/0.87    inference(avatar_contradiction_clause,[],[f145])).
% 3.59/0.87  fof(f145,plain,(
% 3.59/0.87    $false | ~spl6_3),
% 3.59/0.87    inference(resolution,[],[f130,f64])).
% 3.59/0.87  fof(f64,plain,(
% 3.59/0.87    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 3.59/0.87    inference(cnf_transformation,[],[f25])).
% 3.59/0.87  fof(f25,axiom,(
% 3.59/0.87    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 3.59/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 3.59/0.87  fof(f130,plain,(
% 3.59/0.87    v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl6_3),
% 3.59/0.87    inference(avatar_component_clause,[],[f129])).
% 3.59/0.87  fof(f129,plain,(
% 3.59/0.87    spl6_3 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 3.59/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 3.59/0.87  fof(f141,plain,(
% 3.59/0.87    spl6_3 | spl6_5),
% 3.59/0.87    inference(avatar_split_clause,[],[f136,f139,f129])).
% 3.59/0.87  fof(f136,plain,(
% 3.59/0.87    r2_hidden(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 3.59/0.87    inference(resolution,[],[f61,f79])).
% 3.59/0.87  fof(f79,plain,(
% 3.59/0.87    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 3.59/0.87    inference(cnf_transformation,[],[f53])).
% 3.59/0.87  fof(f53,plain,(
% 3.59/0.87    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.59/0.87    inference(nnf_transformation,[],[f31])).
% 3.59/0.87  fof(f31,plain,(
% 3.59/0.87    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.59/0.87    inference(ennf_transformation,[],[f23])).
% 3.59/0.87  fof(f23,axiom,(
% 3.59/0.87    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.59/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 3.59/0.87  fof(f134,plain,(
% 3.59/0.87    spl6_3 | spl6_4),
% 3.59/0.87    inference(avatar_split_clause,[],[f126,f132,f129])).
% 3.59/0.87  fof(f126,plain,(
% 3.59/0.87    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 3.59/0.87    inference(resolution,[],[f60,f79])).
% 3.59/0.87  fof(f123,plain,(
% 3.59/0.87    spl6_1 | spl6_2),
% 3.59/0.87    inference(avatar_split_clause,[],[f62,f118,f115])).
% 3.59/0.87  fof(f62,plain,(
% 3.59/0.87    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)),
% 3.59/0.87    inference(cnf_transformation,[],[f48])).
% 3.59/0.87  fof(f120,plain,(
% 3.59/0.87    ~spl6_1 | ~spl6_2),
% 3.59/0.87    inference(avatar_split_clause,[],[f63,f118,f115])).
% 3.59/0.87  fof(f63,plain,(
% 3.59/0.87    ~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)),
% 3.59/0.87    inference(cnf_transformation,[],[f48])).
% 3.59/0.87  % SZS output end Proof for theBenchmark
% 3.59/0.87  % (6019)------------------------------
% 3.59/0.87  % (6019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.59/0.87  % (6019)Termination reason: Refutation
% 3.59/0.87  
% 3.59/0.87  % (6019)Memory used [KB]: 13176
% 3.59/0.87  % (6019)Time elapsed: 0.448 s
% 3.59/0.87  % (6019)------------------------------
% 3.59/0.87  % (6019)------------------------------
% 3.59/0.87  % (6008)Success in time 0.506 s
%------------------------------------------------------------------------------
