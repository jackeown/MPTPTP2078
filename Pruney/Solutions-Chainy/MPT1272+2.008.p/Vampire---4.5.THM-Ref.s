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
% DateTime   : Thu Dec  3 13:12:39 EST 2020

% Result     : Theorem 3.19s
% Output     : Refutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :  158 (1155 expanded)
%              Number of leaves         :   24 ( 348 expanded)
%              Depth                    :   21
%              Number of atoms          :  438 (3722 expanded)
%              Number of equality atoms :   50 ( 276 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5866,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f264,f340,f693,f883,f2835,f5793,f5865])).

fof(f5865,plain,
    ( ~ spl3_17
    | ~ spl3_94 ),
    inference(avatar_contradiction_clause,[],[f5864])).

fof(f5864,plain,
    ( $false
    | ~ spl3_17
    | ~ spl3_94 ),
    inference(subsumption_resolution,[],[f5863,f269])).

fof(f269,plain,
    ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_17 ),
    inference(backward_demodulation,[],[f251,f188])).

fof(f188,plain,(
    k3_subset_1(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
    inference(resolution,[],[f163,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f163,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f64,f101])).

fof(f101,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f100,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f100,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f63,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f63,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    & v3_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f52,f51])).

fof(f51,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
            & v3_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),X1),sK0)
          & v3_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X1] :
        ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),X1),sK0)
        & v3_tops_1(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
      & v3_tops_1(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          & v3_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          & v3_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tops_1(X1,X0)
             => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_tops_1)).

fof(f64,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f53])).

fof(f251,plain,
    ( m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl3_17
  <=> m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f5863,plain,
    ( ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_94 ),
    inference(forward_demodulation,[],[f5862,f101])).

fof(f5862,plain,
    ( ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_94 ),
    inference(subsumption_resolution,[],[f5861,f63])).

fof(f5861,plain,
    ( ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_94 ),
    inference(subsumption_resolution,[],[f5850,f271])).

fof(f271,plain,(
    ~ v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) ),
    inference(backward_demodulation,[],[f162,f188])).

fof(f162,plain,(
    ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) ),
    inference(backward_demodulation,[],[f66,f101])).

fof(f66,plain,(
    ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f5850,plain,
    ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_94 ),
    inference(trivial_inequality_removal,[],[f5849])).

fof(f5849,plain,
    ( k2_struct_0(sK0) != k2_struct_0(sK0)
    | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_94 ),
    inference(superposition,[],[f73,f882])).

fof(f882,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ spl3_94 ),
    inference(avatar_component_clause,[],[f880])).

fof(f880,plain,
    ( spl3_94
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_94])])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(f5793,plain,
    ( ~ spl3_17
    | ~ spl3_24
    | ~ spl3_27
    | spl3_79
    | ~ spl3_300 ),
    inference(avatar_contradiction_clause,[],[f5792])).

fof(f5792,plain,
    ( $false
    | ~ spl3_17
    | ~ spl3_24
    | ~ spl3_27
    | spl3_79
    | ~ spl3_300 ),
    inference(subsumption_resolution,[],[f5791,f1290])).

fof(f1290,plain,
    ( ~ r1_tarski(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | ~ spl3_24
    | ~ spl3_27
    | spl3_79 ),
    inference(backward_demodulation,[],[f785,f1249])).

fof(f1249,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k4_xboole_0(k2_struct_0(sK0),k1_tops_1(sK0,sK1))
    | ~ spl3_24
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f751,f706])).

fof(f706,plain,
    ( k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1)) = k4_xboole_0(k2_struct_0(sK0),k1_tops_1(sK0,sK1))
    | ~ spl3_27 ),
    inference(resolution,[],[f339,f85])).

fof(f339,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f337])).

fof(f337,plain,
    ( spl3_27
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f751,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1))
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f724,f294])).

fof(f294,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) ),
    inference(forward_demodulation,[],[f293,f188])).

fof(f293,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) ),
    inference(forward_demodulation,[],[f113,f101])).

fof(f113,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f103,f63])).

fof(f103,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f64,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(f724,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))))
    | ~ spl3_24 ),
    inference(resolution,[],[f326,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f326,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f325])).

fof(f325,plain,
    ( spl3_24
  <=> m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f785,plain,
    ( ~ r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))
    | spl3_79 ),
    inference(avatar_component_clause,[],[f784])).

fof(f784,plain,
    ( spl3_79
  <=> r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_79])])).

fof(f5791,plain,
    ( r1_tarski(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | ~ spl3_17
    | ~ spl3_24
    | ~ spl3_27
    | ~ spl3_300 ),
    inference(forward_demodulation,[],[f5790,f3994])).

fof(f3994,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)))
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f3993,f269])).

fof(f3993,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)))
    | ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f3988,f2695])).

fof(f2695,plain,(
    v1_tops_1(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0) ),
    inference(subsumption_resolution,[],[f2678,f125])).

fof(f125,plain,(
    v2_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f124,f63])).

fof(f124,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f105,f65])).

fof(f65,plain,(
    v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f105,plain,
    ( ~ v3_tops_1(sK1,sK0)
    | v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f64,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tops_1(X1,X0)
      | v2_tops_1(k2_pre_topc(X0,X1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tops_1(X1,X0)
              | ~ v2_tops_1(k2_pre_topc(X0,X1),X0) )
            & ( v2_tops_1(k2_pre_topc(X0,X1),X0)
              | ~ v3_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_1)).

fof(f2678,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0)
    | ~ v2_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
    inference(resolution,[],[f1624,f2089])).

fof(f2089,plain,(
    r1_tarski(k2_pre_topc(sK0,sK1),k2_struct_0(sK0)) ),
    inference(resolution,[],[f688,f163])).

fof(f688,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0)))
      | r1_tarski(k2_pre_topc(sK0,X4),k2_struct_0(sK0)) ) ),
    inference(resolution,[],[f185,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f185,plain,(
    ! [X10] :
      ( m1_subset_1(k2_pre_topc(sK0,X10),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f174,f63])).

fof(f174,plain,(
    ! [X10] :
      ( m1_subset_1(k2_pre_topc(sK0,X10),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f90,f101])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f1624,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_struct_0(sK0))
      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0)
      | ~ v2_tops_1(X0,sK0) ) ),
    inference(resolution,[],[f180,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f180,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v2_tops_1(X5,sK0)
      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X5),sK0) ) ),
    inference(subsumption_resolution,[],[f169,f63])).

fof(f169,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v2_tops_1(X5,sK0)
      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X5),sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f78,f101])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_1(X1,X0)
      | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

fof(f3988,plain,
    ( ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0)
    | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)))
    | ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_17 ),
    inference(superposition,[],[f1546,f1853])).

fof(f1853,plain,
    ( k1_tops_1(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1))
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f1841,f270])).

fof(f270,plain,(
    sK1 = k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) ),
    inference(backward_demodulation,[],[f187,f188])).

fof(f187,plain,(
    sK1 = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f163,f86])).

fof(f1841,plain,
    ( k1_tops_1(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1))))
    | ~ spl3_17 ),
    inference(resolution,[],[f176,f269])).

fof(f176,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_tops_1(sK0,X1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X1))) ) ),
    inference(subsumption_resolution,[],[f165,f63])).

fof(f165,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_tops_1(sK0,X1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X1)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f71,f101])).

fof(f1546,plain,(
    ! [X3] :
      ( ~ v1_tops_1(k1_tops_1(sK0,X3),sK0)
      | k2_struct_0(sK0) = k2_pre_topc(sK0,k1_tops_1(sK0,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(resolution,[],[f177,f184])).

fof(f184,plain,(
    ! [X9] :
      ( m1_subset_1(k1_tops_1(sK0,X9),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f173,f63])).

fof(f173,plain,(
    ! [X9] :
      ( m1_subset_1(k1_tops_1(sK0,X9),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f89,f101])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f177,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v1_tops_1(X2,sK0)
      | k2_struct_0(sK0) = k2_pre_topc(sK0,X2) ) ),
    inference(subsumption_resolution,[],[f166,f63])).

fof(f166,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v1_tops_1(X2,sK0)
      | k2_struct_0(sK0) = k2_pre_topc(sK0,X2)
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f72,f101])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f5790,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1))),k4_xboole_0(k2_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | ~ spl3_17
    | ~ spl3_24
    | ~ spl3_27
    | ~ spl3_300 ),
    inference(forward_demodulation,[],[f5789,f1249])).

fof(f5789,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ spl3_17
    | ~ spl3_300 ),
    inference(subsumption_resolution,[],[f5788,f2805])).

fof(f2805,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_300 ),
    inference(avatar_component_clause,[],[f2804])).

fof(f2804,plain,
    ( spl3_300
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_300])])).

fof(f5788,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f5765,f269])).

fof(f5765,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_17 ),
    inference(resolution,[],[f1878,f2706])).

fof(f2706,plain,
    ( r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ spl3_17 ),
    inference(backward_demodulation,[],[f296,f1853])).

fof(f296,plain,
    ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)),k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ spl3_17 ),
    inference(resolution,[],[f175,f269])).

fof(f175,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | r1_tarski(k1_tops_1(sK0,X0),X0) ) ),
    inference(subsumption_resolution,[],[f164,f63])).

fof(f164,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | r1_tarski(k1_tops_1(sK0,X0),X0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f70,f101])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f1878,plain,(
    ! [X6,X5] :
      ( ~ r1_tarski(k3_subset_1(k2_struct_0(sK0),X5),X6)
      | r1_tarski(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X5)),k2_pre_topc(sK0,X6))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(resolution,[],[f182,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f182,plain,(
    ! [X8,X7] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_tarski(X8,X7)
      | r1_tarski(k2_pre_topc(sK0,X8),k2_pre_topc(sK0,X7))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f171,f63])).

fof(f171,plain,(
    ! [X8,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_tarski(X8,X7)
      | r1_tarski(k2_pre_topc(sK0,X8),k2_pre_topc(sK0,X7))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f80,f101])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

fof(f2835,plain,(
    spl3_300 ),
    inference(avatar_contradiction_clause,[],[f2834])).

fof(f2834,plain,
    ( $false
    | spl3_300 ),
    inference(subsumption_resolution,[],[f2831,f2089])).

fof(f2831,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_struct_0(sK0))
    | spl3_300 ),
    inference(resolution,[],[f2806,f95])).

fof(f2806,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_300 ),
    inference(avatar_component_clause,[],[f2804])).

fof(f883,plain,
    ( ~ spl3_79
    | spl3_94
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f878,f325,f880,f784])).

fof(f878,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ spl3_24 ),
    inference(resolution,[],[f723,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
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

fof(f723,plain,
    ( r1_tarski(k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)),k2_struct_0(sK0))
    | ~ spl3_24 ),
    inference(resolution,[],[f326,f94])).

fof(f693,plain,
    ( ~ spl3_17
    | spl3_24 ),
    inference(avatar_contradiction_clause,[],[f692])).

fof(f692,plain,
    ( $false
    | ~ spl3_17
    | spl3_24 ),
    inference(subsumption_resolution,[],[f683,f269])).

fof(f683,plain,
    ( ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_24 ),
    inference(resolution,[],[f185,f327])).

fof(f327,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_24 ),
    inference(avatar_component_clause,[],[f325])).

fof(f340,plain,
    ( ~ spl3_24
    | spl3_27 ),
    inference(avatar_split_clause,[],[f323,f337,f325])).

fof(f323,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(superposition,[],[f84,f294])).

fof(f264,plain,(
    spl3_17 ),
    inference(avatar_contradiction_clause,[],[f263])).

fof(f263,plain,
    ( $false
    | spl3_17 ),
    inference(subsumption_resolution,[],[f261,f163])).

fof(f261,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_17 ),
    inference(resolution,[],[f252,f84])).

fof(f252,plain,
    ( ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_17 ),
    inference(avatar_component_clause,[],[f250])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:48:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (10062)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.48  % (10054)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.48  % (10053)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.48  % (10061)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.50  % (10048)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (10047)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (10060)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.52  % (10044)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.52  % (10064)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.52  % (10046)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.52  % (10052)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.52  % (10049)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.53  % (10058)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.53  % (10068)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.53  % (10051)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.53  % (10055)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.53  % (10056)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.54  % (10050)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.54  % (10069)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.54  % (10045)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (10065)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.54  % (10066)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.43/0.54  % (10067)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.43/0.55  % (10063)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.43/0.55  % (10057)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.61/0.56  % (10059)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.61/0.58  % (10053)Refutation not found, incomplete strategy% (10053)------------------------------
% 1.61/0.58  % (10053)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.58  % (10053)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.58  
% 1.61/0.58  % (10053)Memory used [KB]: 6140
% 1.61/0.58  % (10053)Time elapsed: 0.154 s
% 1.61/0.58  % (10053)------------------------------
% 1.61/0.58  % (10053)------------------------------
% 3.19/0.77  % (10045)Refutation found. Thanks to Tanya!
% 3.19/0.77  % SZS status Theorem for theBenchmark
% 3.19/0.77  % SZS output start Proof for theBenchmark
% 3.19/0.77  fof(f5866,plain,(
% 3.19/0.77    $false),
% 3.19/0.77    inference(avatar_sat_refutation,[],[f264,f340,f693,f883,f2835,f5793,f5865])).
% 3.19/0.77  fof(f5865,plain,(
% 3.19/0.77    ~spl3_17 | ~spl3_94),
% 3.19/0.77    inference(avatar_contradiction_clause,[],[f5864])).
% 3.19/0.77  fof(f5864,plain,(
% 3.19/0.77    $false | (~spl3_17 | ~spl3_94)),
% 3.19/0.77    inference(subsumption_resolution,[],[f5863,f269])).
% 3.19/0.77  fof(f269,plain,(
% 3.19/0.77    m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_17),
% 3.19/0.77    inference(backward_demodulation,[],[f251,f188])).
% 3.19/0.77  fof(f188,plain,(
% 3.19/0.77    k3_subset_1(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1)),
% 3.19/0.77    inference(resolution,[],[f163,f85])).
% 3.19/0.77  fof(f85,plain,(
% 3.19/0.77    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 3.19/0.77    inference(cnf_transformation,[],[f40])).
% 3.19/0.77  fof(f40,plain,(
% 3.19/0.77    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.19/0.77    inference(ennf_transformation,[],[f4])).
% 3.19/0.77  fof(f4,axiom,(
% 3.19/0.77    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.19/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 3.19/0.77  fof(f163,plain,(
% 3.19/0.77    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 3.19/0.77    inference(backward_demodulation,[],[f64,f101])).
% 3.19/0.77  fof(f101,plain,(
% 3.19/0.77    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 3.19/0.77    inference(resolution,[],[f100,f67])).
% 3.19/0.77  fof(f67,plain,(
% 3.19/0.77    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 3.19/0.77    inference(cnf_transformation,[],[f27])).
% 3.19/0.77  fof(f27,plain,(
% 3.19/0.77    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.19/0.77    inference(ennf_transformation,[],[f10])).
% 3.19/0.77  fof(f10,axiom,(
% 3.19/0.77    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.19/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 3.19/0.77  fof(f100,plain,(
% 3.19/0.77    l1_struct_0(sK0)),
% 3.19/0.77    inference(resolution,[],[f63,f68])).
% 3.19/0.77  fof(f68,plain,(
% 3.19/0.77    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 3.19/0.77    inference(cnf_transformation,[],[f28])).
% 3.19/0.77  fof(f28,plain,(
% 3.19/0.77    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.19/0.77    inference(ennf_transformation,[],[f12])).
% 3.19/0.77  fof(f12,axiom,(
% 3.19/0.77    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.19/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 3.19/0.77  fof(f63,plain,(
% 3.19/0.77    l1_pre_topc(sK0)),
% 3.19/0.77    inference(cnf_transformation,[],[f53])).
% 3.19/0.77  fof(f53,plain,(
% 3.19/0.77    (~v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) & v3_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 3.19/0.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f52,f51])).
% 3.19/0.77  fof(f51,plain,(
% 3.19/0.77    ? [X0] : (? [X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) & v3_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(sK0),X1),sK0) & v3_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 3.19/0.77    introduced(choice_axiom,[])).
% 3.19/0.77  fof(f52,plain,(
% 3.19/0.77    ? [X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(sK0),X1),sK0) & v3_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) & v3_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 3.19/0.77    introduced(choice_axiom,[])).
% 3.19/0.77  fof(f26,plain,(
% 3.19/0.77    ? [X0] : (? [X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) & v3_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.19/0.77    inference(flattening,[],[f25])).
% 3.19/0.77  fof(f25,plain,(
% 3.19/0.77    ? [X0] : (? [X1] : ((~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) & v3_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.19/0.77    inference(ennf_transformation,[],[f24])).
% 3.19/0.77  fof(f24,negated_conjecture,(
% 3.19/0.77    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 3.19/0.77    inference(negated_conjecture,[],[f23])).
% 3.19/0.77  fof(f23,conjecture,(
% 3.19/0.77    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 3.19/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_tops_1)).
% 3.19/0.77  fof(f64,plain,(
% 3.19/0.77    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.19/0.77    inference(cnf_transformation,[],[f53])).
% 3.19/0.77  fof(f251,plain,(
% 3.19/0.77    m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_17),
% 3.19/0.77    inference(avatar_component_clause,[],[f250])).
% 3.19/0.77  fof(f250,plain,(
% 3.19/0.77    spl3_17 <=> m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 3.19/0.77    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 3.19/0.77  fof(f5863,plain,(
% 3.19/0.77    ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_94),
% 3.19/0.77    inference(forward_demodulation,[],[f5862,f101])).
% 3.19/0.77  fof(f5862,plain,(
% 3.19/0.77    ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_94),
% 3.19/0.77    inference(subsumption_resolution,[],[f5861,f63])).
% 3.19/0.77  fof(f5861,plain,(
% 3.19/0.77    ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_94),
% 3.19/0.77    inference(subsumption_resolution,[],[f5850,f271])).
% 3.19/0.77  fof(f271,plain,(
% 3.19/0.77    ~v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)),
% 3.19/0.77    inference(backward_demodulation,[],[f162,f188])).
% 3.19/0.77  fof(f162,plain,(
% 3.19/0.77    ~v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)),
% 3.19/0.77    inference(backward_demodulation,[],[f66,f101])).
% 3.19/0.77  fof(f66,plain,(
% 3.19/0.77    ~v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 3.19/0.77    inference(cnf_transformation,[],[f53])).
% 3.19/0.77  fof(f5850,plain,(
% 3.19/0.77    v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_94),
% 3.19/0.77    inference(trivial_inequality_removal,[],[f5849])).
% 3.19/0.77  fof(f5849,plain,(
% 3.19/0.77    k2_struct_0(sK0) != k2_struct_0(sK0) | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_94),
% 3.19/0.77    inference(superposition,[],[f73,f882])).
% 3.19/0.77  fof(f882,plain,(
% 3.19/0.77    k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) | ~spl3_94),
% 3.19/0.77    inference(avatar_component_clause,[],[f880])).
% 3.19/0.77  fof(f880,plain,(
% 3.19/0.77    spl3_94 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))),
% 3.19/0.77    introduced(avatar_definition,[new_symbols(naming,[spl3_94])])).
% 3.19/0.77  fof(f73,plain,(
% 3.19/0.77    ( ! [X0,X1] : (k2_struct_0(X0) != k2_pre_topc(X0,X1) | v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.19/0.77    inference(cnf_transformation,[],[f54])).
% 3.19/0.77  fof(f54,plain,(
% 3.19/0.77    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.19/0.77    inference(nnf_transformation,[],[f32])).
% 3.19/0.77  fof(f32,plain,(
% 3.19/0.77    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.19/0.77    inference(ennf_transformation,[],[f15])).
% 3.19/0.77  fof(f15,axiom,(
% 3.19/0.77    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 3.19/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 3.19/0.77  fof(f5793,plain,(
% 3.19/0.77    ~spl3_17 | ~spl3_24 | ~spl3_27 | spl3_79 | ~spl3_300),
% 3.19/0.77    inference(avatar_contradiction_clause,[],[f5792])).
% 3.19/0.77  fof(f5792,plain,(
% 3.19/0.77    $false | (~spl3_17 | ~spl3_24 | ~spl3_27 | spl3_79 | ~spl3_300)),
% 3.19/0.77    inference(subsumption_resolution,[],[f5791,f1290])).
% 3.19/0.77  fof(f1290,plain,(
% 3.19/0.77    ~r1_tarski(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),k1_tops_1(sK0,sK1))) | (~spl3_24 | ~spl3_27 | spl3_79)),
% 3.19/0.77    inference(backward_demodulation,[],[f785,f1249])).
% 3.19/0.77  fof(f1249,plain,(
% 3.19/0.77    k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k4_xboole_0(k2_struct_0(sK0),k1_tops_1(sK0,sK1)) | (~spl3_24 | ~spl3_27)),
% 3.19/0.77    inference(forward_demodulation,[],[f751,f706])).
% 3.19/0.77  fof(f706,plain,(
% 3.19/0.77    k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1)) = k4_xboole_0(k2_struct_0(sK0),k1_tops_1(sK0,sK1)) | ~spl3_27),
% 3.19/0.77    inference(resolution,[],[f339,f85])).
% 3.19/0.77  fof(f339,plain,(
% 3.19/0.77    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_27),
% 3.19/0.77    inference(avatar_component_clause,[],[f337])).
% 3.19/0.77  fof(f337,plain,(
% 3.19/0.77    spl3_27 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 3.19/0.77    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 3.19/0.77  fof(f751,plain,(
% 3.19/0.77    k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1)) | ~spl3_24),
% 3.19/0.77    inference(forward_demodulation,[],[f724,f294])).
% 3.19/0.77  fof(f294,plain,(
% 3.19/0.77    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))),
% 3.19/0.77    inference(forward_demodulation,[],[f293,f188])).
% 3.19/0.77  fof(f293,plain,(
% 3.19/0.77    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))),
% 3.19/0.77    inference(forward_demodulation,[],[f113,f101])).
% 3.19/0.77  fof(f113,plain,(
% 3.19/0.77    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 3.19/0.77    inference(subsumption_resolution,[],[f103,f63])).
% 3.19/0.77  fof(f103,plain,(
% 3.19/0.77    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | ~l1_pre_topc(sK0)),
% 3.19/0.77    inference(resolution,[],[f64,f71])).
% 3.19/0.77  fof(f71,plain,(
% 3.19/0.77    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~l1_pre_topc(X0)) )),
% 3.19/0.77    inference(cnf_transformation,[],[f31])).
% 3.19/0.77  fof(f31,plain,(
% 3.19/0.77    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.19/0.77    inference(ennf_transformation,[],[f14])).
% 3.19/0.77  fof(f14,axiom,(
% 3.19/0.77    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 3.19/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 3.19/0.77  fof(f724,plain,(
% 3.19/0.77    k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))) | ~spl3_24),
% 3.19/0.77    inference(resolution,[],[f326,f86])).
% 3.19/0.77  fof(f86,plain,(
% 3.19/0.77    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 3.19/0.77    inference(cnf_transformation,[],[f41])).
% 3.19/0.77  fof(f41,plain,(
% 3.19/0.77    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.19/0.77    inference(ennf_transformation,[],[f6])).
% 3.19/0.77  fof(f6,axiom,(
% 3.19/0.77    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.19/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 3.19/0.77  fof(f326,plain,(
% 3.19/0.77    m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_24),
% 3.19/0.77    inference(avatar_component_clause,[],[f325])).
% 3.19/0.77  fof(f325,plain,(
% 3.19/0.77    spl3_24 <=> m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0)))),
% 3.19/0.77    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 3.19/0.77  fof(f785,plain,(
% 3.19/0.77    ~r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) | spl3_79),
% 3.19/0.77    inference(avatar_component_clause,[],[f784])).
% 3.19/0.77  fof(f784,plain,(
% 3.19/0.77    spl3_79 <=> r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))),
% 3.19/0.77    introduced(avatar_definition,[new_symbols(naming,[spl3_79])])).
% 3.19/0.77  fof(f5791,plain,(
% 3.19/0.77    r1_tarski(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),k1_tops_1(sK0,sK1))) | (~spl3_17 | ~spl3_24 | ~spl3_27 | ~spl3_300)),
% 3.19/0.77    inference(forward_demodulation,[],[f5790,f3994])).
% 3.19/0.77  fof(f3994,plain,(
% 3.19/0.77    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1))) | ~spl3_17),
% 3.19/0.77    inference(subsumption_resolution,[],[f3993,f269])).
% 3.19/0.77  fof(f3993,plain,(
% 3.19/0.77    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1))) | ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_17),
% 3.19/0.77    inference(subsumption_resolution,[],[f3988,f2695])).
% 3.19/0.77  fof(f2695,plain,(
% 3.19/0.77    v1_tops_1(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0)),
% 3.19/0.77    inference(subsumption_resolution,[],[f2678,f125])).
% 3.19/0.77  fof(f125,plain,(
% 3.19/0.77    v2_tops_1(k2_pre_topc(sK0,sK1),sK0)),
% 3.19/0.77    inference(subsumption_resolution,[],[f124,f63])).
% 3.19/0.77  fof(f124,plain,(
% 3.19/0.77    v2_tops_1(k2_pre_topc(sK0,sK1),sK0) | ~l1_pre_topc(sK0)),
% 3.19/0.77    inference(subsumption_resolution,[],[f105,f65])).
% 3.19/0.77  fof(f65,plain,(
% 3.19/0.77    v3_tops_1(sK1,sK0)),
% 3.19/0.77    inference(cnf_transformation,[],[f53])).
% 3.19/0.77  fof(f105,plain,(
% 3.19/0.77    ~v3_tops_1(sK1,sK0) | v2_tops_1(k2_pre_topc(sK0,sK1),sK0) | ~l1_pre_topc(sK0)),
% 3.19/0.77    inference(resolution,[],[f64,f74])).
% 3.19/0.77  fof(f74,plain,(
% 3.19/0.77    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tops_1(X1,X0) | v2_tops_1(k2_pre_topc(X0,X1),X0) | ~l1_pre_topc(X0)) )),
% 3.19/0.77    inference(cnf_transformation,[],[f55])).
% 3.19/0.77  fof(f55,plain,(
% 3.19/0.77    ! [X0] : (! [X1] : (((v3_tops_1(X1,X0) | ~v2_tops_1(k2_pre_topc(X0,X1),X0)) & (v2_tops_1(k2_pre_topc(X0,X1),X0) | ~v3_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.19/0.77    inference(nnf_transformation,[],[f33])).
% 3.19/0.77  fof(f33,plain,(
% 3.19/0.77    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.19/0.77    inference(ennf_transformation,[],[f17])).
% 3.19/0.77  fof(f17,axiom,(
% 3.19/0.77    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0))))),
% 3.19/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_1)).
% 3.19/0.77  fof(f2678,plain,(
% 3.19/0.77    v1_tops_1(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0) | ~v2_tops_1(k2_pre_topc(sK0,sK1),sK0)),
% 3.19/0.77    inference(resolution,[],[f1624,f2089])).
% 3.19/0.77  fof(f2089,plain,(
% 3.19/0.77    r1_tarski(k2_pre_topc(sK0,sK1),k2_struct_0(sK0))),
% 3.19/0.77    inference(resolution,[],[f688,f163])).
% 3.19/0.77  fof(f688,plain,(
% 3.19/0.77    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0))) | r1_tarski(k2_pre_topc(sK0,X4),k2_struct_0(sK0))) )),
% 3.19/0.77    inference(resolution,[],[f185,f94])).
% 3.19/0.77  fof(f94,plain,(
% 3.19/0.77    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 3.19/0.77    inference(cnf_transformation,[],[f62])).
% 3.19/0.77  fof(f62,plain,(
% 3.19/0.77    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.19/0.77    inference(nnf_transformation,[],[f9])).
% 3.19/0.77  fof(f9,axiom,(
% 3.19/0.77    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.19/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 3.19/0.77  fof(f185,plain,(
% 3.19/0.77    ( ! [X10] : (m1_subset_1(k2_pre_topc(sK0,X10),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X10,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 3.19/0.77    inference(subsumption_resolution,[],[f174,f63])).
% 3.19/0.77  fof(f174,plain,(
% 3.19/0.77    ( ! [X10] : (m1_subset_1(k2_pre_topc(sK0,X10),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X10,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 3.19/0.77    inference(superposition,[],[f90,f101])).
% 3.19/0.77  fof(f90,plain,(
% 3.19/0.77    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.19/0.77    inference(cnf_transformation,[],[f49])).
% 3.19/0.77  fof(f49,plain,(
% 3.19/0.77    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.19/0.77    inference(flattening,[],[f48])).
% 3.19/0.77  fof(f48,plain,(
% 3.19/0.77    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.19/0.77    inference(ennf_transformation,[],[f11])).
% 3.19/0.77  fof(f11,axiom,(
% 3.19/0.77    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.19/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 3.19/0.77  fof(f1624,plain,(
% 3.19/0.77    ( ! [X0] : (~r1_tarski(X0,k2_struct_0(sK0)) | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) | ~v2_tops_1(X0,sK0)) )),
% 3.19/0.77    inference(resolution,[],[f180,f95])).
% 3.19/0.77  fof(f95,plain,(
% 3.19/0.77    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.19/0.77    inference(cnf_transformation,[],[f62])).
% 3.19/0.77  fof(f180,plain,(
% 3.19/0.77    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_tops_1(X5,sK0) | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X5),sK0)) )),
% 3.19/0.77    inference(subsumption_resolution,[],[f169,f63])).
% 3.19/0.77  fof(f169,plain,(
% 3.19/0.77    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_tops_1(X5,sK0) | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X5),sK0) | ~l1_pre_topc(sK0)) )),
% 3.19/0.77    inference(superposition,[],[f78,f101])).
% 3.19/0.77  fof(f78,plain,(
% 3.19/0.77    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tops_1(X1,X0) | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~l1_pre_topc(X0)) )),
% 3.19/0.77    inference(cnf_transformation,[],[f57])).
% 3.19/0.77  fof(f57,plain,(
% 3.19/0.77    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.19/0.77    inference(nnf_transformation,[],[f35])).
% 3.19/0.77  fof(f35,plain,(
% 3.19/0.77    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.19/0.77    inference(ennf_transformation,[],[f16])).
% 3.19/0.77  fof(f16,axiom,(
% 3.19/0.77    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 3.19/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).
% 3.19/0.77  fof(f3988,plain,(
% 3.19/0.77    ~v1_tops_1(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1))) | ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_17),
% 3.19/0.77    inference(superposition,[],[f1546,f1853])).
% 3.19/0.77  fof(f1853,plain,(
% 3.19/0.77    k1_tops_1(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)) | ~spl3_17),
% 3.19/0.77    inference(forward_demodulation,[],[f1841,f270])).
% 3.19/0.77  fof(f270,plain,(
% 3.19/0.77    sK1 = k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1))),
% 3.19/0.77    inference(backward_demodulation,[],[f187,f188])).
% 3.19/0.77  fof(f187,plain,(
% 3.19/0.77    sK1 = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))),
% 3.19/0.77    inference(resolution,[],[f163,f86])).
% 3.19/0.77  fof(f1841,plain,(
% 3.19/0.77    k1_tops_1(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)))) | ~spl3_17),
% 3.19/0.77    inference(resolution,[],[f176,f269])).
% 3.19/0.77  fof(f176,plain,(
% 3.19/0.77    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | k1_tops_1(sK0,X1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X1)))) )),
% 3.19/0.77    inference(subsumption_resolution,[],[f165,f63])).
% 3.19/0.77  fof(f165,plain,(
% 3.19/0.77    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | k1_tops_1(sK0,X1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X1))) | ~l1_pre_topc(sK0)) )),
% 3.19/0.77    inference(superposition,[],[f71,f101])).
% 3.19/0.77  fof(f1546,plain,(
% 3.19/0.77    ( ! [X3] : (~v1_tops_1(k1_tops_1(sK0,X3),sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,k1_tops_1(sK0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 3.19/0.77    inference(resolution,[],[f177,f184])).
% 3.19/0.77  fof(f184,plain,(
% 3.19/0.77    ( ! [X9] : (m1_subset_1(k1_tops_1(sK0,X9),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X9,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 3.19/0.77    inference(subsumption_resolution,[],[f173,f63])).
% 3.19/0.77  fof(f173,plain,(
% 3.19/0.77    ( ! [X9] : (m1_subset_1(k1_tops_1(sK0,X9),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X9,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 3.19/0.77    inference(superposition,[],[f89,f101])).
% 3.19/0.77  fof(f89,plain,(
% 3.19/0.77    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.19/0.77    inference(cnf_transformation,[],[f47])).
% 3.19/0.77  fof(f47,plain,(
% 3.19/0.77    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.19/0.77    inference(flattening,[],[f46])).
% 3.19/0.77  fof(f46,plain,(
% 3.19/0.77    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.19/0.77    inference(ennf_transformation,[],[f18])).
% 3.19/0.77  fof(f18,axiom,(
% 3.19/0.77    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.19/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 3.19/0.77  fof(f177,plain,(
% 3.19/0.77    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tops_1(X2,sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,X2)) )),
% 3.19/0.77    inference(subsumption_resolution,[],[f166,f63])).
% 3.19/0.77  fof(f166,plain,(
% 3.19/0.77    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tops_1(X2,sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,X2) | ~l1_pre_topc(sK0)) )),
% 3.19/0.77    inference(superposition,[],[f72,f101])).
% 3.19/0.77  fof(f72,plain,(
% 3.19/0.77    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~l1_pre_topc(X0)) )),
% 3.19/0.77    inference(cnf_transformation,[],[f54])).
% 3.19/0.77  fof(f5790,plain,(
% 3.19/0.77    r1_tarski(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1))),k4_xboole_0(k2_struct_0(sK0),k1_tops_1(sK0,sK1))) | (~spl3_17 | ~spl3_24 | ~spl3_27 | ~spl3_300)),
% 3.19/0.77    inference(forward_demodulation,[],[f5789,f1249])).
% 3.19/0.77  fof(f5789,plain,(
% 3.19/0.77    r1_tarski(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) | (~spl3_17 | ~spl3_300)),
% 3.19/0.77    inference(subsumption_resolution,[],[f5788,f2805])).
% 3.19/0.77  fof(f2805,plain,(
% 3.19/0.77    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_300),
% 3.19/0.77    inference(avatar_component_clause,[],[f2804])).
% 3.19/0.77  fof(f2804,plain,(
% 3.19/0.77    spl3_300 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 3.19/0.77    introduced(avatar_definition,[new_symbols(naming,[spl3_300])])).
% 3.19/0.77  fof(f5788,plain,(
% 3.19/0.77    r1_tarski(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_17),
% 3.19/0.77    inference(subsumption_resolution,[],[f5765,f269])).
% 3.19/0.77  fof(f5765,plain,(
% 3.19/0.77    r1_tarski(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) | ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_17),
% 3.19/0.77    inference(resolution,[],[f1878,f2706])).
% 3.19/0.77  fof(f2706,plain,(
% 3.19/0.77    r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),k4_xboole_0(k2_struct_0(sK0),sK1)) | ~spl3_17),
% 3.19/0.77    inference(backward_demodulation,[],[f296,f1853])).
% 3.19/0.77  fof(f296,plain,(
% 3.19/0.77    r1_tarski(k1_tops_1(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)),k4_xboole_0(k2_struct_0(sK0),sK1)) | ~spl3_17),
% 3.19/0.77    inference(resolution,[],[f175,f269])).
% 3.19/0.77  fof(f175,plain,(
% 3.19/0.77    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),X0)) )),
% 3.19/0.77    inference(subsumption_resolution,[],[f164,f63])).
% 3.19/0.77  fof(f164,plain,(
% 3.19/0.77    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),X0) | ~l1_pre_topc(sK0)) )),
% 3.19/0.77    inference(superposition,[],[f70,f101])).
% 3.19/0.77  fof(f70,plain,(
% 3.19/0.77    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 3.19/0.77    inference(cnf_transformation,[],[f30])).
% 3.19/0.77  fof(f30,plain,(
% 3.19/0.77    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.19/0.77    inference(ennf_transformation,[],[f21])).
% 3.19/0.77  fof(f21,axiom,(
% 3.19/0.77    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 3.19/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 3.19/0.77  fof(f1878,plain,(
% 3.19/0.77    ( ! [X6,X5] : (~r1_tarski(k3_subset_1(k2_struct_0(sK0),X5),X6) | r1_tarski(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X5)),k2_pre_topc(sK0,X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 3.19/0.77    inference(resolution,[],[f182,f84])).
% 3.19/0.77  fof(f84,plain,(
% 3.19/0.77    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.19/0.77    inference(cnf_transformation,[],[f39])).
% 3.19/0.77  fof(f39,plain,(
% 3.19/0.77    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.19/0.77    inference(ennf_transformation,[],[f5])).
% 3.19/0.77  fof(f5,axiom,(
% 3.19/0.77    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.19/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 3.19/0.77  fof(f182,plain,(
% 3.19/0.77    ( ! [X8,X7] : (~m1_subset_1(X8,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X8,X7) | r1_tarski(k2_pre_topc(sK0,X8),k2_pre_topc(sK0,X7)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 3.19/0.77    inference(subsumption_resolution,[],[f171,f63])).
% 3.19/0.77  fof(f171,plain,(
% 3.19/0.77    ( ! [X8,X7] : (~m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X8,X7) | r1_tarski(k2_pre_topc(sK0,X8),k2_pre_topc(sK0,X7)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 3.19/0.77    inference(superposition,[],[f80,f101])).
% 3.19/0.77  fof(f80,plain,(
% 3.19/0.77    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.19/0.77    inference(cnf_transformation,[],[f37])).
% 3.19/0.77  fof(f37,plain,(
% 3.19/0.77    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.19/0.77    inference(flattening,[],[f36])).
% 3.19/0.77  fof(f36,plain,(
% 3.19/0.77    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.19/0.77    inference(ennf_transformation,[],[f13])).
% 3.19/0.77  fof(f13,axiom,(
% 3.19/0.77    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 3.19/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).
% 3.19/0.77  fof(f2835,plain,(
% 3.19/0.77    spl3_300),
% 3.19/0.77    inference(avatar_contradiction_clause,[],[f2834])).
% 3.19/0.77  fof(f2834,plain,(
% 3.19/0.77    $false | spl3_300),
% 3.19/0.77    inference(subsumption_resolution,[],[f2831,f2089])).
% 3.19/0.77  fof(f2831,plain,(
% 3.19/0.77    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_struct_0(sK0)) | spl3_300),
% 3.19/0.77    inference(resolution,[],[f2806,f95])).
% 3.19/0.77  fof(f2806,plain,(
% 3.19/0.77    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) | spl3_300),
% 3.19/0.77    inference(avatar_component_clause,[],[f2804])).
% 3.19/0.77  fof(f883,plain,(
% 3.19/0.77    ~spl3_79 | spl3_94 | ~spl3_24),
% 3.19/0.77    inference(avatar_split_clause,[],[f878,f325,f880,f784])).
% 3.19/0.77  fof(f878,plain,(
% 3.19/0.77    k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) | ~r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) | ~spl3_24),
% 3.19/0.77    inference(resolution,[],[f723,f93])).
% 3.19/0.77  fof(f93,plain,(
% 3.19/0.77    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.19/0.77    inference(cnf_transformation,[],[f61])).
% 3.19/0.77  fof(f61,plain,(
% 3.19/0.77    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.19/0.77    inference(flattening,[],[f60])).
% 3.19/0.77  fof(f60,plain,(
% 3.19/0.77    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.19/0.77    inference(nnf_transformation,[],[f1])).
% 3.19/0.77  fof(f1,axiom,(
% 3.19/0.77    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.19/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.19/0.77  fof(f723,plain,(
% 3.19/0.77    r1_tarski(k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)),k2_struct_0(sK0)) | ~spl3_24),
% 3.19/0.77    inference(resolution,[],[f326,f94])).
% 3.19/0.77  fof(f693,plain,(
% 3.19/0.77    ~spl3_17 | spl3_24),
% 3.19/0.77    inference(avatar_contradiction_clause,[],[f692])).
% 3.19/0.77  fof(f692,plain,(
% 3.19/0.77    $false | (~spl3_17 | spl3_24)),
% 3.19/0.77    inference(subsumption_resolution,[],[f683,f269])).
% 3.19/0.77  fof(f683,plain,(
% 3.19/0.77    ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | spl3_24),
% 3.19/0.77    inference(resolution,[],[f185,f327])).
% 3.19/0.77  fof(f327,plain,(
% 3.19/0.77    ~m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0))) | spl3_24),
% 3.19/0.77    inference(avatar_component_clause,[],[f325])).
% 3.19/0.77  fof(f340,plain,(
% 3.19/0.77    ~spl3_24 | spl3_27),
% 3.19/0.77    inference(avatar_split_clause,[],[f323,f337,f325])).
% 3.19/0.77  fof(f323,plain,(
% 3.19/0.77    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0)))),
% 3.19/0.77    inference(superposition,[],[f84,f294])).
% 3.19/0.77  fof(f264,plain,(
% 3.19/0.77    spl3_17),
% 3.19/0.77    inference(avatar_contradiction_clause,[],[f263])).
% 3.19/0.77  fof(f263,plain,(
% 3.19/0.77    $false | spl3_17),
% 3.19/0.77    inference(subsumption_resolution,[],[f261,f163])).
% 3.19/0.77  fof(f261,plain,(
% 3.19/0.77    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | spl3_17),
% 3.19/0.77    inference(resolution,[],[f252,f84])).
% 3.19/0.77  fof(f252,plain,(
% 3.19/0.77    ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | spl3_17),
% 3.19/0.77    inference(avatar_component_clause,[],[f250])).
% 3.19/0.77  % SZS output end Proof for theBenchmark
% 3.19/0.77  % (10045)------------------------------
% 3.19/0.77  % (10045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.19/0.77  % (10045)Termination reason: Refutation
% 3.19/0.77  
% 3.19/0.77  % (10045)Memory used [KB]: 13432
% 3.19/0.77  % (10045)Time elapsed: 0.319 s
% 3.19/0.77  % (10045)------------------------------
% 3.19/0.77  % (10045)------------------------------
% 3.19/0.77  % (10043)Success in time 0.408 s
%------------------------------------------------------------------------------
