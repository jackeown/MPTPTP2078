%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 179 expanded)
%              Number of leaves         :   27 (  68 expanded)
%              Depth                    :    9
%              Number of atoms          :  285 ( 568 expanded)
%              Number of equality atoms :   16 (  35 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f815,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f66,f86,f93,f166,f348,f560,f588,f598,f800,f811,f814])).

fof(f814,plain,
    ( ~ spl3_18
    | spl3_1
    | ~ spl3_69 ),
    inference(avatar_split_clause,[],[f812,f797,f58,f329])).

fof(f329,plain,
    ( spl3_18
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f58,plain,
    ( spl3_1
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f797,plain,
    ( spl3_69
  <=> r1_xboole_0(k3_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).

fof(f812,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ r1_tarski(sK1,sK0)
    | ~ spl3_69 ),
    inference(superposition,[],[f799,f100])).

fof(f100,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X3,X2) = X2
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f49,f41])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f799,plain,
    ( r1_xboole_0(k3_xboole_0(sK0,sK1),sK2)
    | ~ spl3_69 ),
    inference(avatar_component_clause,[],[f797])).

fof(f811,plain,(
    spl3_68 ),
    inference(avatar_contradiction_clause,[],[f808])).

fof(f808,plain,
    ( $false
    | spl3_68 ),
    inference(resolution,[],[f795,f38])).

fof(f38,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f795,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k1_xboole_0)
    | spl3_68 ),
    inference(avatar_component_clause,[],[f793])).

fof(f793,plain,
    ( spl3_68
  <=> r1_xboole_0(k3_xboole_0(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).

fof(f800,plain,
    ( ~ spl3_68
    | spl3_69
    | ~ spl3_18
    | ~ spl3_38
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f772,f566,f562,f329,f797,f793])).

fof(f562,plain,
    ( spl3_38
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f566,plain,
    ( spl3_39
  <=> r1_tarski(sK2,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f772,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ r1_tarski(sK1,sK0)
    | r1_xboole_0(k3_xboole_0(sK0,sK1),sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl3_39 ),
    inference(resolution,[],[f215,f608])).

fof(f608,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,k3_subset_1(sK0,sK1))
        | r1_xboole_0(X0,sK2)
        | ~ r1_xboole_0(X0,k1_xboole_0) )
    | ~ spl3_39 ),
    inference(resolution,[],[f567,f139])).

fof(f139,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X3,X4)
      | ~ r1_xboole_0(X5,X4)
      | r1_xboole_0(X5,X3)
      | ~ r1_xboole_0(X5,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f133,f39])).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f133,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_xboole_0(X5,k5_xboole_0(X3,X3))
      | ~ r1_xboole_0(X5,X4)
      | r1_xboole_0(X5,X3)
      | ~ r1_tarski(X3,X4) ) ),
    inference(superposition,[],[f56,f49])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
      | ~ r1_xboole_0(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f43])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
        & r1_xboole_0(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_xboole_1)).

fof(f567,plain,
    ( r1_tarski(sK2,k3_subset_1(sK0,sK1))
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f566])).

fof(f215,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_xboole_0(X0,X1),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f112,f100])).

fof(f112,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(k3_xboole_0(X2,k3_xboole_0(X2,X3)),k3_subset_1(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f42,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f50,f43])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f42,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f598,plain,
    ( ~ spl3_38
    | ~ spl3_7
    | ~ spl3_2
    | spl3_39 ),
    inference(avatar_split_clause,[],[f590,f566,f62,f154,f562])).

fof(f154,plain,
    ( spl3_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f62,plain,
    ( spl3_2
  <=> r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f590,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl3_39 ),
    inference(resolution,[],[f568,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

fof(f568,plain,
    ( ~ r1_tarski(sK2,k3_subset_1(sK0,sK1))
    | spl3_39 ),
    inference(avatar_component_clause,[],[f566])).

fof(f588,plain,(
    spl3_38 ),
    inference(avatar_contradiction_clause,[],[f585])).

fof(f585,plain,
    ( $false
    | spl3_38 ),
    inference(resolution,[],[f564,f33])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK2))
      | ~ r1_xboole_0(sK1,sK2) )
    & ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
      | r1_xboole_0(sK1,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f30,f29])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | r1_xboole_0(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(sK1,k3_subset_1(sK0,X2))
            | ~ r1_xboole_0(sK1,X2) )
          & ( r1_tarski(sK1,k3_subset_1(sK0,X2))
            | r1_xboole_0(sK1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(sK1,k3_subset_1(sK0,X2))
          | ~ r1_xboole_0(sK1,X2) )
        & ( r1_tarski(sK1,k3_subset_1(sK0,X2))
          | r1_xboole_0(sK1,X2) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK2))
        | ~ r1_xboole_0(sK1,sK2) )
      & ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
        | r1_xboole_0(sK1,sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
            | ~ r1_xboole_0(X1,X2) )
          & ( r1_tarski(X1,k3_subset_1(X0,X2))
            | r1_xboole_0(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
            | ~ r1_xboole_0(X1,X2) )
          & ( r1_tarski(X1,k3_subset_1(X0,X2))
            | r1_xboole_0(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_xboole_0(X1,X2)
          <~> r1_tarski(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_xboole_0(X1,X2)
            <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

fof(f564,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl3_38 ),
    inference(avatar_component_clause,[],[f562])).

fof(f560,plain,
    ( ~ spl3_7
    | ~ spl3_18
    | ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f556,f62,f58,f329,f154])).

fof(f556,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | ~ r1_tarski(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | spl3_2 ),
    inference(resolution,[],[f64,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k3_subset_1(X0,X1))
      | ~ r1_xboole_0(X2,X1)
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f55,f54])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f52,f43])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f64,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f348,plain,
    ( ~ spl3_4
    | spl3_18 ),
    inference(avatar_contradiction_clause,[],[f347])).

fof(f347,plain,
    ( $false
    | ~ spl3_4
    | spl3_18 ),
    inference(resolution,[],[f331,f106])).

fof(f106,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_4 ),
    inference(resolution,[],[f74,f85])).

fof(f85,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl3_4
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_zfmisc_1(X0))
      | r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f48,f40])).

fof(f40,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f331,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl3_18 ),
    inference(avatar_component_clause,[],[f329])).

fof(f166,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | spl3_7 ),
    inference(resolution,[],[f156,f34])).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f156,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f154])).

fof(f93,plain,(
    ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f92])).

fof(f92,plain,
    ( $false
    | ~ spl3_3 ),
    inference(resolution,[],[f81,f37])).

fof(f37,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f81,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl3_3
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f86,plain,
    ( spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f75,f83,f79])).

fof(f75,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f44,f33])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f66,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f35,f62,f58])).

fof(f35,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f65,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f36,f62,f58])).

fof(f36,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:29:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (16455)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.44  % (16455)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f815,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f65,f66,f86,f93,f166,f348,f560,f588,f598,f800,f811,f814])).
% 0.21/0.44  fof(f814,plain,(
% 0.21/0.44    ~spl3_18 | spl3_1 | ~spl3_69),
% 0.21/0.44    inference(avatar_split_clause,[],[f812,f797,f58,f329])).
% 0.21/0.44  fof(f329,plain,(
% 0.21/0.44    spl3_18 <=> r1_tarski(sK1,sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.44  fof(f58,plain,(
% 0.21/0.44    spl3_1 <=> r1_xboole_0(sK1,sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.44  fof(f797,plain,(
% 0.21/0.44    spl3_69 <=> r1_xboole_0(k3_xboole_0(sK0,sK1),sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).
% 0.21/0.44  fof(f812,plain,(
% 0.21/0.44    r1_xboole_0(sK1,sK2) | ~r1_tarski(sK1,sK0) | ~spl3_69),
% 0.21/0.44    inference(superposition,[],[f799,f100])).
% 0.21/0.44  fof(f100,plain,(
% 0.21/0.44    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) )),
% 0.21/0.44    inference(superposition,[],[f49,f41])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.44  fof(f799,plain,(
% 0.21/0.44    r1_xboole_0(k3_xboole_0(sK0,sK1),sK2) | ~spl3_69),
% 0.21/0.44    inference(avatar_component_clause,[],[f797])).
% 0.21/0.44  fof(f811,plain,(
% 0.21/0.44    spl3_68),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f808])).
% 0.21/0.44  fof(f808,plain,(
% 0.21/0.44    $false | spl3_68),
% 0.21/0.44    inference(resolution,[],[f795,f38])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.44  fof(f795,plain,(
% 0.21/0.44    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k1_xboole_0) | spl3_68),
% 0.21/0.44    inference(avatar_component_clause,[],[f793])).
% 0.21/0.44  fof(f793,plain,(
% 0.21/0.44    spl3_68 <=> r1_xboole_0(k3_xboole_0(sK0,sK1),k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).
% 0.21/0.44  fof(f800,plain,(
% 0.21/0.44    ~spl3_68 | spl3_69 | ~spl3_18 | ~spl3_38 | ~spl3_39),
% 0.21/0.44    inference(avatar_split_clause,[],[f772,f566,f562,f329,f797,f793])).
% 0.21/0.44  fof(f562,plain,(
% 0.21/0.44    spl3_38 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.21/0.44  fof(f566,plain,(
% 0.21/0.44    spl3_39 <=> r1_tarski(sK2,k3_subset_1(sK0,sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.21/0.44  fof(f772,plain,(
% 0.21/0.44    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~r1_tarski(sK1,sK0) | r1_xboole_0(k3_xboole_0(sK0,sK1),sK2) | ~r1_xboole_0(k3_xboole_0(sK0,sK1),k1_xboole_0) | ~spl3_39),
% 0.21/0.44    inference(resolution,[],[f215,f608])).
% 0.21/0.44  fof(f608,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_xboole_0(X0,k3_subset_1(sK0,sK1)) | r1_xboole_0(X0,sK2) | ~r1_xboole_0(X0,k1_xboole_0)) ) | ~spl3_39),
% 0.21/0.44    inference(resolution,[],[f567,f139])).
% 0.21/0.44  fof(f139,plain,(
% 0.21/0.44    ( ! [X4,X5,X3] : (~r1_tarski(X3,X4) | ~r1_xboole_0(X5,X4) | r1_xboole_0(X5,X3) | ~r1_xboole_0(X5,k1_xboole_0)) )),
% 0.21/0.44    inference(forward_demodulation,[],[f133,f39])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,axiom,(
% 0.21/0.44    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.21/0.44  fof(f133,plain,(
% 0.21/0.44    ( ! [X4,X5,X3] : (~r1_xboole_0(X5,k5_xboole_0(X3,X3)) | ~r1_xboole_0(X5,X4) | r1_xboole_0(X5,X3) | ~r1_tarski(X3,X4)) )),
% 0.21/0.44    inference(superposition,[],[f56,f49])).
% 0.21/0.44  fof(f56,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) | ~r1_xboole_0(X0,X2) | r1_xboole_0(X0,X1)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f53,f43])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.44  fof(f53,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | r1_xboole_0(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f26])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | r1_xboole_0(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_xboole_1)).
% 0.21/0.44  fof(f567,plain,(
% 0.21/0.44    r1_tarski(sK2,k3_subset_1(sK0,sK1)) | ~spl3_39),
% 0.21/0.44    inference(avatar_component_clause,[],[f566])).
% 0.21/0.44  fof(f215,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r1_tarski(X1,X0)) )),
% 0.21/0.44    inference(superposition,[],[f112,f100])).
% 0.21/0.44  fof(f112,plain,(
% 0.21/0.44    ( ! [X2,X3] : (r1_xboole_0(k3_xboole_0(X2,k3_xboole_0(X2,X3)),k3_subset_1(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(X2))) )),
% 0.21/0.44    inference(superposition,[],[f42,f54])).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f50,f43])).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f21])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,axiom,(
% 0.21/0.44    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).
% 0.21/0.44  fof(f598,plain,(
% 0.21/0.44    ~spl3_38 | ~spl3_7 | ~spl3_2 | spl3_39),
% 0.21/0.44    inference(avatar_split_clause,[],[f590,f566,f62,f154,f562])).
% 0.21/0.44  fof(f154,plain,(
% 0.21/0.44    spl3_7 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.44  fof(f62,plain,(
% 0.21/0.44    spl3_2 <=> r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.44  fof(f590,plain,(
% 0.21/0.44    ~r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl3_39),
% 0.21/0.44    inference(resolution,[],[f568,f51])).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f23])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ! [X0,X1] : (! [X2] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.44    inference(flattening,[],[f22])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ! [X0,X1] : (! [X2] : ((r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,axiom,(
% 0.21/0.44    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).
% 0.21/0.44  fof(f568,plain,(
% 0.21/0.44    ~r1_tarski(sK2,k3_subset_1(sK0,sK1)) | spl3_39),
% 0.21/0.44    inference(avatar_component_clause,[],[f566])).
% 0.21/0.44  fof(f588,plain,(
% 0.21/0.44    spl3_38),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f585])).
% 0.21/0.44  fof(f585,plain,(
% 0.21/0.44    $false | spl3_38),
% 0.21/0.44    inference(resolution,[],[f564,f33])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.44    inference(cnf_transformation,[],[f31])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ((~r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~r1_xboole_0(sK1,sK2)) & (r1_tarski(sK1,k3_subset_1(sK0,sK2)) | r1_xboole_0(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f30,f29])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2)) & (r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(sK1,k3_subset_1(sK0,X2)) | ~r1_xboole_0(sK1,X2)) & (r1_tarski(sK1,k3_subset_1(sK0,X2)) | r1_xboole_0(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    ? [X2] : ((~r1_tarski(sK1,k3_subset_1(sK0,X2)) | ~r1_xboole_0(sK1,X2)) & (r1_tarski(sK1,k3_subset_1(sK0,X2)) | r1_xboole_0(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => ((~r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~r1_xboole_0(sK1,sK2)) & (r1_tarski(sK1,k3_subset_1(sK0,sK2)) | r1_xboole_0(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2)) & (r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.44    inference(flattening,[],[f27])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ? [X0,X1] : (? [X2] : (((~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2)) & (r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.44    inference(nnf_transformation,[],[f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ? [X0,X1] : (? [X2] : ((r1_xboole_0(X1,X2) <~> r1_tarski(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f16])).
% 0.21/0.44  fof(f16,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 0.21/0.44    inference(negated_conjecture,[],[f15])).
% 0.21/0.44  fof(f15,conjecture,(
% 0.21/0.44    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).
% 0.21/0.44  fof(f564,plain,(
% 0.21/0.44    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl3_38),
% 0.21/0.44    inference(avatar_component_clause,[],[f562])).
% 0.21/0.44  fof(f560,plain,(
% 0.21/0.44    ~spl3_7 | ~spl3_18 | ~spl3_1 | spl3_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f556,f62,f58,f329,f154])).
% 0.21/0.44  fof(f556,plain,(
% 0.21/0.44    ~r1_xboole_0(sK1,sK2) | ~r1_tarski(sK1,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | spl3_2),
% 0.21/0.44    inference(resolution,[],[f64,f118])).
% 0.21/0.44  fof(f118,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_xboole_0(X2,X1) | ~r1_tarski(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.44    inference(superposition,[],[f55,f54])).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f52,f43])).
% 0.21/0.44  fof(f52,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f25])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.44    inference(flattening,[],[f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.44    inference(ennf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).
% 0.21/0.44  fof(f64,plain,(
% 0.21/0.44    ~r1_tarski(sK1,k3_subset_1(sK0,sK2)) | spl3_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f62])).
% 0.21/0.44  fof(f348,plain,(
% 0.21/0.44    ~spl3_4 | spl3_18),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f347])).
% 0.21/0.44  fof(f347,plain,(
% 0.21/0.44    $false | (~spl3_4 | spl3_18)),
% 0.21/0.44    inference(resolution,[],[f331,f106])).
% 0.21/0.44  fof(f106,plain,(
% 0.21/0.44    r1_tarski(sK1,sK0) | ~spl3_4),
% 0.21/0.44    inference(resolution,[],[f74,f85])).
% 0.21/0.44  fof(f85,plain,(
% 0.21/0.44    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl3_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f83])).
% 0.21/0.44  fof(f83,plain,(
% 0.21/0.44    spl3_4 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.44  fof(f74,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r2_hidden(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X0)) )),
% 0.21/0.44    inference(superposition,[],[f48,f40])).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,axiom,(
% 0.21/0.44    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,axiom,(
% 0.21/0.44    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.21/0.44  fof(f331,plain,(
% 0.21/0.44    ~r1_tarski(sK1,sK0) | spl3_18),
% 0.21/0.44    inference(avatar_component_clause,[],[f329])).
% 0.21/0.44  fof(f166,plain,(
% 0.21/0.44    spl3_7),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f163])).
% 0.21/0.44  fof(f163,plain,(
% 0.21/0.44    $false | spl3_7),
% 0.21/0.44    inference(resolution,[],[f156,f34])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.44    inference(cnf_transformation,[],[f31])).
% 0.21/0.44  fof(f156,plain,(
% 0.21/0.44    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | spl3_7),
% 0.21/0.44    inference(avatar_component_clause,[],[f154])).
% 0.21/0.44  fof(f93,plain,(
% 0.21/0.44    ~spl3_3),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f92])).
% 0.21/0.44  fof(f92,plain,(
% 0.21/0.44    $false | ~spl3_3),
% 0.21/0.44    inference(resolution,[],[f81,f37])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,axiom,(
% 0.21/0.44    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.21/0.44  fof(f81,plain,(
% 0.21/0.44    v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl3_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f79])).
% 0.21/0.44  fof(f79,plain,(
% 0.21/0.44    spl3_3 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.44  fof(f86,plain,(
% 0.21/0.44    spl3_3 | spl3_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f75,f83,f79])).
% 0.21/0.44  fof(f75,plain,(
% 0.21/0.44    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.21/0.44    inference(resolution,[],[f44,f33])).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f32])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.44    inference(nnf_transformation,[],[f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,axiom,(
% 0.21/0.44    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.44  fof(f66,plain,(
% 0.21/0.44    spl3_1 | spl3_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f35,f62,f58])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    r1_tarski(sK1,k3_subset_1(sK0,sK2)) | r1_xboole_0(sK1,sK2)),
% 0.21/0.44    inference(cnf_transformation,[],[f31])).
% 0.21/0.44  fof(f65,plain,(
% 0.21/0.44    ~spl3_1 | ~spl3_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f36,f62,f58])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    ~r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~r1_xboole_0(sK1,sK2)),
% 0.21/0.44    inference(cnf_transformation,[],[f31])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (16455)------------------------------
% 0.21/0.44  % (16455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (16455)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (16455)Memory used [KB]: 6524
% 0.21/0.44  % (16455)Time elapsed: 0.021 s
% 0.21/0.44  % (16455)------------------------------
% 0.21/0.44  % (16455)------------------------------
% 0.21/0.45  % (16448)Success in time 0.081 s
%------------------------------------------------------------------------------
