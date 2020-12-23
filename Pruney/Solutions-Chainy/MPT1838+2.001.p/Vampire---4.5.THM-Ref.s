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
% DateTime   : Thu Dec  3 13:19:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  114 (3046 expanded)
%              Number of leaves         :   18 ( 894 expanded)
%              Depth                    :   24
%              Number of atoms          :  362 (15923 expanded)
%              Number of equality atoms :   96 (3674 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f384,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f274,f337,f383])).

fof(f383,plain,
    ( spl7_3
    | ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f382])).

fof(f382,plain,
    ( $false
    | spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f268,f369])).

fof(f369,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1)
    | ~ spl7_4 ),
    inference(backward_demodulation,[],[f253,f359])).

fof(f359,plain,
    ( ! [X0] : sK1 = k4_xboole_0(X0,X0)
    | ~ spl7_4 ),
    inference(backward_demodulation,[],[f239,f273])).

fof(f273,plain,
    ( sK1 = k4_xboole_0(k1_xboole_0,sK1)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f271])).

fof(f271,plain,
    ( spl7_4
  <=> sK1 = k4_xboole_0(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f239,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(X0,X0) ),
    inference(duplicate_literal_removal,[],[f230])).

fof(f230,plain,(
    ! [X0] :
      ( k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(X0,X0)
      | k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(X0,X0) ) ),
    inference(resolution,[],[f205,f204])).

fof(f204,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK6(k1_xboole_0,sK1,k4_xboole_0(X2,X3)),X2)
      | k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f198,f112])).

fof(f112,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK6(X0,X1,X2),X1)
            | ~ r2_hidden(sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
              & r2_hidden(sK6(X0,X1,X2),X0) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f52,f53])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
            & r2_hidden(sK6(X0,X1,X2),X0) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f198,plain,(
    ! [X1] :
      ( r2_hidden(sK6(k1_xboole_0,sK1,X1),X1)
      | k4_xboole_0(k1_xboole_0,sK1) = X1 ) ),
    inference(forward_demodulation,[],[f197,f182])).

fof(f182,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f181,f59])).

fof(f59,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( sK0 != sK1
    & r1_tarski(sK0,sK1)
    & v1_zfmisc_1(sK1)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f27,f26])).

fof(f26,plain,
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

fof(f27,plain,
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

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( r1_tarski(X0,X1)
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f181,plain,
    ( k1_xboole_0 = sK0
    | sK0 = sK1 ),
    inference(resolution,[],[f133,f58])).

fof(f58,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f133,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | k1_xboole_0 = X0
      | sK1 = X0 ) ),
    inference(superposition,[],[f79,f129])).

fof(f129,plain,(
    sK1 = k1_tarski(sK2(sK1)) ),
    inference(forward_demodulation,[],[f128,f118])).

fof(f118,plain,(
    sK1 = k6_domain_1(sK1,sK2(sK1)) ),
    inference(subsumption_resolution,[],[f116,f56])).

fof(f56,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f116,plain,
    ( sK1 = k6_domain_1(sK1,sK2(sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f57,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | k6_domain_1(X0,sK2(X0)) = X0
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK2(X0)) = X0
            & m1_subset_1(sK2(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK2(X0)) = X0
        & m1_subset_1(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

fof(f57,plain,(
    v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f128,plain,(
    k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1)) ),
    inference(subsumption_resolution,[],[f127,f56])).

fof(f127,plain,
    ( k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f117,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k1_tarski(X1) = k6_domain_1(X0,X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f117,plain,(
    m1_subset_1(sK2(sK1),sK1) ),
    inference(subsumption_resolution,[],[f115,f56])).

fof(f115,plain,
    ( m1_subset_1(sK2(sK1),sK1)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f57,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | m1_subset_1(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f197,plain,(
    ! [X1] :
      ( k4_xboole_0(k1_xboole_0,sK1) = X1
      | r2_hidden(sK6(sK0,sK1,X1),X1) ) ),
    inference(backward_demodulation,[],[f168,f182])).

fof(f168,plain,(
    ! [X1] :
      ( k4_xboole_0(sK0,sK1) = X1
      | r2_hidden(sK6(sK0,sK1,X1),X1) ) ),
    inference(duplicate_literal_removal,[],[f167])).

fof(f167,plain,(
    ! [X1] :
      ( k4_xboole_0(sK0,sK1) = X1
      | r2_hidden(sK6(sK0,sK1,X1),X1)
      | r2_hidden(sK6(sK0,sK1,X1),X1)
      | k4_xboole_0(sK0,sK1) = X1 ) ),
    inference(resolution,[],[f151,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X2)
      | r2_hidden(sK6(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f151,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK6(X2,sK1,X3),sK0)
      | k4_xboole_0(X2,sK1) = X3
      | r2_hidden(sK6(X2,sK1,X3),X3) ) ),
    inference(resolution,[],[f119,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1,X2),X1)
      | k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK6(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f119,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f58,f76])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

% (15108)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f39,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f205,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK6(k1_xboole_0,sK1,k4_xboole_0(X4,X5)),X5)
      | k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(X4,X5) ) ),
    inference(resolution,[],[f198,f111])).

fof(f111,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f253,plain,(
    ! [X8] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(X8,X8)) ),
    inference(forward_demodulation,[],[f246,f138])).

fof(f138,plain,(
    k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,sK1)) ),
    inference(resolution,[],[f134,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f71,f68])).

fof(f68,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f134,plain,(
    r1_tarski(k1_xboole_0,sK1) ),
    inference(superposition,[],[f106,f129])).

fof(f106,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f246,plain,(
    ! [X8] : k1_setfam_1(k2_tarski(k1_xboole_0,sK1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X8,X8)) ),
    inference(superposition,[],[f94,f239])).

fof(f94,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f69,f68])).

fof(f69,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f268,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,sK1)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f267])).

fof(f267,plain,
    ( spl7_3
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f337,plain,(
    ~ spl7_3 ),
    inference(avatar_contradiction_clause,[],[f329])).

fof(f329,plain,
    ( $false
    | ~ spl7_3 ),
    inference(resolution,[],[f313,f186])).

fof(f186,plain,(
    r2_hidden(sK3(k1_xboole_0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f113,f182])).

fof(f113,plain,(
    r2_hidden(sK3(sK0),sK0) ),
    inference(resolution,[],[f55,f65])).

fof(f65,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
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

fof(f55,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f313,plain,
    ( ! [X5] : ~ r2_hidden(X5,k1_xboole_0)
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f310,f136])).

fof(f136,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f134,f76])).

fof(f310,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,k1_xboole_0)
        | ~ r2_hidden(X5,sK1) )
    | ~ spl7_3 ),
    inference(backward_demodulation,[],[f244,f297])).

fof(f297,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl7_3 ),
    inference(backward_demodulation,[],[f239,f269])).

fof(f269,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f267])).

fof(f244,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,k4_xboole_0(X4,X4))
      | ~ r2_hidden(X5,sK1) ) ),
    inference(superposition,[],[f111,f239])).

fof(f274,plain,
    ( spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f257,f271,f267])).

fof(f257,plain,
    ( sK1 = k4_xboole_0(k1_xboole_0,sK1)
    | k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1) ),
    inference(resolution,[],[f254,f179])).

fof(f179,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0,sK1),X0)
      | sK1 = X0
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f133,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f254,plain,(
    ! [X5] : ~ r2_hidden(X5,k4_xboole_0(k1_xboole_0,sK1)) ),
    inference(subsumption_resolution,[],[f250,f249])).

fof(f249,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k4_xboole_0(k1_xboole_0,sK1))
      | r2_hidden(X3,X2) ) ),
    inference(superposition,[],[f112,f239])).

fof(f250,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,k4_xboole_0(k1_xboole_0,sK1))
      | ~ r2_hidden(X5,X4) ) ),
    inference(superposition,[],[f111,f239])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:03:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (15080)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.50  % (15090)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.50  % (15083)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (15090)Refutation not found, incomplete strategy% (15090)------------------------------
% 0.20/0.51  % (15090)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (15086)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (15092)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (15095)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.51  % (15098)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.51  % (15090)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (15090)Memory used [KB]: 10618
% 0.20/0.51  % (15090)Time elapsed: 0.094 s
% 0.20/0.51  % (15090)------------------------------
% 0.20/0.51  % (15090)------------------------------
% 0.20/0.51  % (15087)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  % (15106)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.52  % (15084)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (15100)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.52  % (15093)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (15105)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (15103)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (15081)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (15104)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (15081)Refutation not found, incomplete strategy% (15081)------------------------------
% 0.20/0.53  % (15081)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (15081)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (15081)Memory used [KB]: 10746
% 0.20/0.53  % (15081)Time elapsed: 0.115 s
% 0.20/0.53  % (15081)------------------------------
% 0.20/0.53  % (15081)------------------------------
% 0.20/0.53  % (15091)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (15079)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (15082)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (15101)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (15097)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  % (15101)Refutation not found, incomplete strategy% (15101)------------------------------
% 0.20/0.53  % (15101)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (15101)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (15101)Memory used [KB]: 10746
% 0.20/0.53  % (15101)Time elapsed: 0.091 s
% 0.20/0.53  % (15101)------------------------------
% 0.20/0.53  % (15101)------------------------------
% 0.20/0.53  % (15089)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (15089)Refutation not found, incomplete strategy% (15089)------------------------------
% 0.20/0.54  % (15089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (15089)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (15089)Memory used [KB]: 10618
% 0.20/0.54  % (15089)Time elapsed: 0.130 s
% 0.20/0.54  % (15089)------------------------------
% 0.20/0.54  % (15089)------------------------------
% 0.20/0.54  % (15085)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (15107)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (15096)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (15096)Refutation not found, incomplete strategy% (15096)------------------------------
% 0.20/0.54  % (15096)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (15096)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (15096)Memory used [KB]: 10746
% 0.20/0.54  % (15096)Time elapsed: 0.129 s
% 0.20/0.54  % (15096)------------------------------
% 0.20/0.54  % (15096)------------------------------
% 0.20/0.54  % (15087)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f384,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f274,f337,f383])).
% 0.20/0.54  fof(f383,plain,(
% 0.20/0.54    spl7_3 | ~spl7_4),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f382])).
% 0.20/0.54  fof(f382,plain,(
% 0.20/0.54    $false | (spl7_3 | ~spl7_4)),
% 0.20/0.54    inference(subsumption_resolution,[],[f268,f369])).
% 0.20/0.54  fof(f369,plain,(
% 0.20/0.54    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1) | ~spl7_4),
% 0.20/0.54    inference(backward_demodulation,[],[f253,f359])).
% 0.20/0.54  fof(f359,plain,(
% 0.20/0.54    ( ! [X0] : (sK1 = k4_xboole_0(X0,X0)) ) | ~spl7_4),
% 0.20/0.54    inference(backward_demodulation,[],[f239,f273])).
% 0.20/0.54  fof(f273,plain,(
% 0.20/0.54    sK1 = k4_xboole_0(k1_xboole_0,sK1) | ~spl7_4),
% 0.20/0.54    inference(avatar_component_clause,[],[f271])).
% 0.20/0.54  fof(f271,plain,(
% 0.20/0.54    spl7_4 <=> sK1 = k4_xboole_0(k1_xboole_0,sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.54  fof(f239,plain,(
% 0.20/0.54    ( ! [X0] : (k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(X0,X0)) )),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f230])).
% 0.20/0.54  fof(f230,plain,(
% 0.20/0.54    ( ! [X0] : (k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(X0,X0) | k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(X0,X0)) )),
% 0.20/0.54    inference(resolution,[],[f205,f204])).
% 0.20/0.54  fof(f204,plain,(
% 0.20/0.54    ( ! [X2,X3] : (r2_hidden(sK6(k1_xboole_0,sK1,k4_xboole_0(X2,X3)),X2) | k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(X2,X3)) )),
% 0.20/0.54    inference(resolution,[],[f198,f112])).
% 0.20/0.54  fof(f112,plain,(
% 0.20/0.54    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 0.20/0.54    inference(equality_resolution,[],[f88])).
% 0.20/0.54  fof(f88,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.54    inference(cnf_transformation,[],[f54])).
% 0.20/0.54  fof(f54,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f52,f53])).
% 0.20/0.54  fof(f53,plain,(
% 0.20/0.54    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.54    inference(rectify,[],[f51])).
% 0.20/0.54  fof(f51,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.54    inference(flattening,[],[f50])).
% 0.20/0.54  fof(f50,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.54    inference(nnf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.20/0.54  fof(f198,plain,(
% 0.20/0.54    ( ! [X1] : (r2_hidden(sK6(k1_xboole_0,sK1,X1),X1) | k4_xboole_0(k1_xboole_0,sK1) = X1) )),
% 0.20/0.54    inference(forward_demodulation,[],[f197,f182])).
% 0.20/0.54  fof(f182,plain,(
% 0.20/0.54    k1_xboole_0 = sK0),
% 0.20/0.54    inference(subsumption_resolution,[],[f181,f59])).
% 0.20/0.54  fof(f59,plain,(
% 0.20/0.54    sK0 != sK1),
% 0.20/0.54    inference(cnf_transformation,[],[f28])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    (sK0 != sK1 & r1_tarski(sK0,sK1) & v1_zfmisc_1(sK1) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f27,f26])).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (sK0 != X1 & r1_tarski(sK0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ? [X1] : (sK0 != X1 & r1_tarski(sK0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (sK0 != sK1 & r1_tarski(sK0,sK1) & v1_zfmisc_1(sK1) & ~v1_xboole_0(sK1))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.54    inference(flattening,[],[f18])).
% 0.20/0.54  fof(f18,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : ((X0 != X1 & r1_tarski(X0,X1)) & (v1_zfmisc_1(X1) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f17])).
% 0.20/0.54  fof(f17,negated_conjecture,(
% 0.20/0.54    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.20/0.54    inference(negated_conjecture,[],[f16])).
% 0.20/0.54  fof(f16,conjecture,(
% 0.20/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 0.20/0.54  fof(f181,plain,(
% 0.20/0.54    k1_xboole_0 = sK0 | sK0 = sK1),
% 0.20/0.54    inference(resolution,[],[f133,f58])).
% 0.20/0.54  fof(f58,plain,(
% 0.20/0.54    r1_tarski(sK0,sK1)),
% 0.20/0.54    inference(cnf_transformation,[],[f28])).
% 0.20/0.54  fof(f133,plain,(
% 0.20/0.54    ( ! [X0] : (~r1_tarski(X0,sK1) | k1_xboole_0 = X0 | sK1 = X0) )),
% 0.20/0.54    inference(superposition,[],[f79,f129])).
% 0.20/0.54  fof(f129,plain,(
% 0.20/0.54    sK1 = k1_tarski(sK2(sK1))),
% 0.20/0.54    inference(forward_demodulation,[],[f128,f118])).
% 0.20/0.54  fof(f118,plain,(
% 0.20/0.54    sK1 = k6_domain_1(sK1,sK2(sK1))),
% 0.20/0.54    inference(subsumption_resolution,[],[f116,f56])).
% 0.20/0.54  fof(f56,plain,(
% 0.20/0.54    ~v1_xboole_0(sK1)),
% 0.20/0.54    inference(cnf_transformation,[],[f28])).
% 0.20/0.54  fof(f116,plain,(
% 0.20/0.54    sK1 = k6_domain_1(sK1,sK2(sK1)) | v1_xboole_0(sK1)),
% 0.20/0.54    inference(resolution,[],[f57,f62])).
% 0.20/0.54  fof(f62,plain,(
% 0.20/0.54    ( ! [X0] : (~v1_zfmisc_1(X0) | k6_domain_1(X0,sK2(X0)) = X0 | v1_xboole_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f32])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK2(X0)) = X0 & m1_subset_1(sK2(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK2(X0)) = X0 & m1_subset_1(sK2(X0),X0)))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.20/0.54    inference(rectify,[],[f29])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.20/0.54    inference(nnf_transformation,[],[f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f15])).
% 0.20/0.54  fof(f15,axiom,(
% 0.20/0.54    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).
% 0.20/0.54  fof(f57,plain,(
% 0.20/0.54    v1_zfmisc_1(sK1)),
% 0.20/0.54    inference(cnf_transformation,[],[f28])).
% 0.20/0.54  fof(f128,plain,(
% 0.20/0.54    k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1))),
% 0.20/0.54    inference(subsumption_resolution,[],[f127,f56])).
% 0.20/0.54  fof(f127,plain,(
% 0.20/0.54    k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1)) | v1_xboole_0(sK1)),
% 0.20/0.54    inference(resolution,[],[f117,f72])).
% 0.20/0.54  fof(f72,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k1_tarski(X1) = k6_domain_1(X0,X1) | v1_xboole_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.54    inference(flattening,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f14])).
% 0.20/0.54  fof(f14,axiom,(
% 0.20/0.54    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.54  fof(f117,plain,(
% 0.20/0.54    m1_subset_1(sK2(sK1),sK1)),
% 0.20/0.54    inference(subsumption_resolution,[],[f115,f56])).
% 0.20/0.54  fof(f115,plain,(
% 0.20/0.54    m1_subset_1(sK2(sK1),sK1) | v1_xboole_0(sK1)),
% 0.20/0.54    inference(resolution,[],[f57,f61])).
% 0.20/0.54  fof(f61,plain,(
% 0.20/0.54    ( ! [X0] : (~v1_zfmisc_1(X0) | m1_subset_1(sK2(X0),X0) | v1_xboole_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f32])).
% 0.20/0.54  fof(f79,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f44])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.20/0.54    inference(flattening,[],[f43])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.20/0.54    inference(nnf_transformation,[],[f11])).
% 0.20/0.54  fof(f11,axiom,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.20/0.54  fof(f197,plain,(
% 0.20/0.54    ( ! [X1] : (k4_xboole_0(k1_xboole_0,sK1) = X1 | r2_hidden(sK6(sK0,sK1,X1),X1)) )),
% 0.20/0.54    inference(backward_demodulation,[],[f168,f182])).
% 0.20/0.54  fof(f168,plain,(
% 0.20/0.54    ( ! [X1] : (k4_xboole_0(sK0,sK1) = X1 | r2_hidden(sK6(sK0,sK1,X1),X1)) )),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f167])).
% 0.20/0.54  fof(f167,plain,(
% 0.20/0.54    ( ! [X1] : (k4_xboole_0(sK0,sK1) = X1 | r2_hidden(sK6(sK0,sK1,X1),X1) | r2_hidden(sK6(sK0,sK1,X1),X1) | k4_xboole_0(sK0,sK1) = X1) )),
% 0.20/0.54    inference(resolution,[],[f151,f91])).
% 0.20/0.54  fof(f91,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X2) | r2_hidden(sK6(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 0.20/0.54    inference(cnf_transformation,[],[f54])).
% 0.20/0.54  fof(f151,plain,(
% 0.20/0.54    ( ! [X2,X3] : (~r2_hidden(sK6(X2,sK1,X3),sK0) | k4_xboole_0(X2,sK1) = X3 | r2_hidden(sK6(X2,sK1,X3),X3)) )),
% 0.20/0.54    inference(resolution,[],[f119,f92])).
% 0.20/0.54  fof(f92,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r2_hidden(sK6(X0,X1,X2),X1) | k4_xboole_0(X0,X1) = X2 | r2_hidden(sK6(X0,X1,X2),X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f54])).
% 0.20/0.54  fof(f119,plain,(
% 0.20/0.54    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) )),
% 0.20/0.54    inference(resolution,[],[f58,f76])).
% 0.20/0.54  fof(f76,plain,(
% 0.20/0.54    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f42])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.54    inference(rectify,[],[f39])).
% 0.20/0.54  % (15108)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  fof(f39,plain,(
% 0.20/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.54    inference(nnf_transformation,[],[f25])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.54  fof(f205,plain,(
% 0.20/0.54    ( ! [X4,X5] : (~r2_hidden(sK6(k1_xboole_0,sK1,k4_xboole_0(X4,X5)),X5) | k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(X4,X5)) )),
% 0.20/0.54    inference(resolution,[],[f198,f111])).
% 0.20/0.54  fof(f111,plain,(
% 0.20/0.54    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.20/0.54    inference(equality_resolution,[],[f89])).
% 0.20/0.54  fof(f89,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.54    inference(cnf_transformation,[],[f54])).
% 0.20/0.54  fof(f253,plain,(
% 0.20/0.54    ( ! [X8] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(X8,X8))) )),
% 0.20/0.54    inference(forward_demodulation,[],[f246,f138])).
% 0.20/0.54  fof(f138,plain,(
% 0.20/0.54    k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,sK1))),
% 0.20/0.54    inference(resolution,[],[f134,f96])).
% 0.20/0.54  fof(f96,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 0.20/0.54    inference(definition_unfolding,[],[f71,f68])).
% 0.20/0.54  fof(f68,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f13])).
% 0.20/0.54  fof(f13,axiom,(
% 0.20/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.54  fof(f71,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.54  fof(f134,plain,(
% 0.20/0.54    r1_tarski(k1_xboole_0,sK1)),
% 0.20/0.54    inference(superposition,[],[f106,f129])).
% 0.20/0.54  fof(f106,plain,(
% 0.20/0.54    ( ! [X1] : (r1_tarski(k1_xboole_0,k1_tarski(X1))) )),
% 0.20/0.54    inference(equality_resolution,[],[f80])).
% 0.20/0.54  fof(f80,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 != X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f44])).
% 0.20/0.54  fof(f246,plain,(
% 0.20/0.54    ( ! [X8] : (k1_setfam_1(k2_tarski(k1_xboole_0,sK1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X8,X8))) )),
% 0.20/0.54    inference(superposition,[],[f94,f239])).
% 0.20/0.54  fof(f94,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.54    inference(definition_unfolding,[],[f69,f68])).
% 0.20/0.54  fof(f69,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,axiom,(
% 0.20/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.54  fof(f268,plain,(
% 0.20/0.54    k1_xboole_0 != k4_xboole_0(k1_xboole_0,sK1) | spl7_3),
% 0.20/0.54    inference(avatar_component_clause,[],[f267])).
% 0.20/0.54  fof(f267,plain,(
% 0.20/0.54    spl7_3 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.54  fof(f337,plain,(
% 0.20/0.54    ~spl7_3),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f329])).
% 0.20/0.54  fof(f329,plain,(
% 0.20/0.54    $false | ~spl7_3),
% 0.20/0.54    inference(resolution,[],[f313,f186])).
% 0.20/0.54  fof(f186,plain,(
% 0.20/0.54    r2_hidden(sK3(k1_xboole_0),k1_xboole_0)),
% 0.20/0.54    inference(backward_demodulation,[],[f113,f182])).
% 0.20/0.54  fof(f113,plain,(
% 0.20/0.54    r2_hidden(sK3(sK0),sK0)),
% 0.20/0.54    inference(resolution,[],[f55,f65])).
% 0.20/0.54  fof(f65,plain,(
% 0.20/0.54    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f36])).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.54    inference(rectify,[],[f33])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.54    inference(nnf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.54  fof(f55,plain,(
% 0.20/0.54    ~v1_xboole_0(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f28])).
% 0.20/0.54  fof(f313,plain,(
% 0.20/0.54    ( ! [X5] : (~r2_hidden(X5,k1_xboole_0)) ) | ~spl7_3),
% 0.20/0.54    inference(subsumption_resolution,[],[f310,f136])).
% 0.20/0.54  fof(f136,plain,(
% 0.20/0.54    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.54    inference(resolution,[],[f134,f76])).
% 0.20/0.54  fof(f310,plain,(
% 0.20/0.54    ( ! [X5] : (~r2_hidden(X5,k1_xboole_0) | ~r2_hidden(X5,sK1)) ) | ~spl7_3),
% 0.20/0.54    inference(backward_demodulation,[],[f244,f297])).
% 0.20/0.54  fof(f297,plain,(
% 0.20/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl7_3),
% 0.20/0.54    inference(backward_demodulation,[],[f239,f269])).
% 0.20/0.54  fof(f269,plain,(
% 0.20/0.54    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1) | ~spl7_3),
% 0.20/0.54    inference(avatar_component_clause,[],[f267])).
% 0.20/0.54  fof(f244,plain,(
% 0.20/0.54    ( ! [X4,X5] : (~r2_hidden(X5,k4_xboole_0(X4,X4)) | ~r2_hidden(X5,sK1)) )),
% 0.20/0.54    inference(superposition,[],[f111,f239])).
% 0.20/0.54  fof(f274,plain,(
% 0.20/0.54    spl7_3 | spl7_4),
% 0.20/0.54    inference(avatar_split_clause,[],[f257,f271,f267])).
% 0.20/0.54  fof(f257,plain,(
% 0.20/0.54    sK1 = k4_xboole_0(k1_xboole_0,sK1) | k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1)),
% 0.20/0.54    inference(resolution,[],[f254,f179])).
% 0.20/0.54  fof(f179,plain,(
% 0.20/0.54    ( ! [X0] : (r2_hidden(sK4(X0,sK1),X0) | sK1 = X0 | k1_xboole_0 = X0) )),
% 0.20/0.54    inference(resolution,[],[f133,f77])).
% 0.20/0.54  fof(f77,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f42])).
% 0.20/0.54  fof(f254,plain,(
% 0.20/0.54    ( ! [X5] : (~r2_hidden(X5,k4_xboole_0(k1_xboole_0,sK1))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f250,f249])).
% 0.20/0.54  fof(f249,plain,(
% 0.20/0.54    ( ! [X2,X3] : (~r2_hidden(X3,k4_xboole_0(k1_xboole_0,sK1)) | r2_hidden(X3,X2)) )),
% 0.20/0.54    inference(superposition,[],[f112,f239])).
% 0.20/0.54  fof(f250,plain,(
% 0.20/0.54    ( ! [X4,X5] : (~r2_hidden(X5,k4_xboole_0(k1_xboole_0,sK1)) | ~r2_hidden(X5,X4)) )),
% 0.20/0.54    inference(superposition,[],[f111,f239])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (15087)------------------------------
% 0.20/0.54  % (15087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (15087)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (15087)Memory used [KB]: 10874
% 0.20/0.54  % (15087)Time elapsed: 0.117 s
% 0.20/0.54  % (15087)------------------------------
% 0.20/0.54  % (15087)------------------------------
% 0.20/0.54  % (15088)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (15094)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (15078)Success in time 0.185 s
%------------------------------------------------------------------------------
