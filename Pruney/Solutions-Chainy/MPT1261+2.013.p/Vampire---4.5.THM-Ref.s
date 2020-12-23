%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:49 EST 2020

% Result     : Theorem 2.69s
% Output     : Refutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 430 expanded)
%              Number of leaves         :   26 ( 124 expanded)
%              Depth                    :   25
%              Number of atoms          :  355 (1560 expanded)
%              Number of equality atoms :  117 ( 492 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1964,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f98,f1919,f1930,f1963])).

fof(f1963,plain,
    ( spl2_2
    | ~ spl2_44 ),
    inference(avatar_contradiction_clause,[],[f1962])).

fof(f1962,plain,
    ( $false
    | spl2_2
    | ~ spl2_44 ),
    inference(subsumption_resolution,[],[f1961,f96])).

fof(f96,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f1961,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_44 ),
    inference(forward_demodulation,[],[f326,f1927])).

fof(f1927,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_44 ),
    inference(avatar_component_clause,[],[f1925])).

fof(f1925,plain,
    ( spl2_44
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f326,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f324,f49])).

fof(f49,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | ~ v4_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | ~ v4_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | ~ v4_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | v4_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | ~ v4_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | v4_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(f324,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f56,f50])).

fof(f50,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f1930,plain,
    ( spl2_44
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f1929,f90,f1925])).

fof(f90,plain,
    ( spl2_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f1929,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f252,f49])).

fof(f252,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f57,f50])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f1919,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f1918])).

fof(f1918,plain,
    ( $false
    | spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f1917,f49])).

fof(f1917,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f1916,f50])).

fof(f1916,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f1915,f48])).

fof(f48,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f1915,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f1903,f92])).

fof(f92,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f90])).

fof(f1903,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(trivial_inequality_removal,[],[f1902])).

fof(f1902,plain,
    ( sK1 != sK1
    | v4_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(superposition,[],[f58,f1896])).

fof(f1896,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f290,f1892])).

fof(f1892,plain,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f1880,f1032])).

fof(f1032,plain,
    ( sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f1031,f139])).

fof(f139,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f105,f137])).

fof(f137,plain,(
    ! [X2] : k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X2)) ),
    inference(resolution,[],[f120,f80])).

fof(f80,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f59,f63])).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f120,plain,(
    ! [X5] :
      ( ~ r1_tarski(X5,k1_xboole_0)
      | k1_xboole_0 = X5 ) ),
    inference(resolution,[],[f72,f53])).

fof(f53,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f105,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(k1_xboole_0,X0))) = X0 ),
    inference(superposition,[],[f79,f61])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f79,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f54,f78])).

fof(f78,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f65,f63])).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f54,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f1031,plain,
    ( k5_xboole_0(sK1,k1_xboole_0) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f1017,f700])).

fof(f700,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f690,f697])).

fof(f697,plain,(
    ! [X6] : k1_xboole_0 = k3_subset_1(X6,X6) ),
    inference(backward_demodulation,[],[f470,f692])).

fof(f692,plain,(
    ! [X6] : k3_subset_1(X6,k1_xboole_0) = X6 ),
    inference(forward_demodulation,[],[f691,f139])).

fof(f691,plain,(
    ! [X6] : k3_subset_1(X6,k1_xboole_0) = k5_xboole_0(X6,k1_xboole_0) ),
    inference(forward_demodulation,[],[f667,f138])).

fof(f138,plain,(
    ! [X3] : k1_xboole_0 = k1_setfam_1(k2_tarski(X3,k1_xboole_0)) ),
    inference(resolution,[],[f120,f99])).

fof(f99,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0) ),
    inference(superposition,[],[f80,f61])).

fof(f667,plain,(
    ! [X6] : k3_subset_1(X6,k1_xboole_0) = k5_xboole_0(X6,k1_setfam_1(k2_tarski(X6,k1_xboole_0))) ),
    inference(resolution,[],[f238,f53])).

fof(f238,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(resolution,[],[f84,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f67,f78])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f470,plain,(
    ! [X6] : k1_xboole_0 = k3_subset_1(X6,k3_subset_1(X6,k1_xboole_0)) ),
    inference(resolution,[],[f175,f53])).

fof(f175,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(resolution,[],[f68,f74])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f690,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f663,f156])).

fof(f156,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(resolution,[],[f83,f87])).

fof(f87,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f66,f63])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f663,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0))) = k3_subset_1(X0,X0) ),
    inference(resolution,[],[f238,f87])).

fof(f1017,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)))
    | ~ spl2_2 ),
    inference(superposition,[],[f202,f442])).

fof(f442,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f437,f61])).

fof(f437,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1))
    | ~ spl2_2 ),
    inference(resolution,[],[f431,f83])).

fof(f431,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_2 ),
    inference(superposition,[],[f423,f95])).

fof(f95,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f94])).

fof(f423,plain,(
    ! [X1] : r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X1),sK1) ),
    inference(superposition,[],[f81,f258])).

fof(f258,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) ),
    inference(resolution,[],[f85,f50])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f75,f78])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f81,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f60,f78])).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f202,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X1,X0)) = k5_xboole_0(X1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0)))) ),
    inference(superposition,[],[f82,f61])).

fof(f82,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) ),
    inference(definition_unfolding,[],[f64,f62,f78])).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f1880,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_2 ),
    inference(resolution,[],[f865,f441])).

fof(f441,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f436,f87])).

fof(f436,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ r1_tarski(sK1,sK1)
    | ~ spl2_2 ),
    inference(resolution,[],[f431,f168])).

fof(f168,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,X1)
      | r1_tarski(X2,u1_struct_0(sK0))
      | ~ r1_tarski(X1,sK1) ) ),
    inference(resolution,[],[f152,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f152,plain,(
    ! [X13] :
      ( r1_tarski(X13,u1_struct_0(sK0))
      | ~ r1_tarski(X13,sK1) ) ),
    inference(resolution,[],[f76,f101])).

fof(f101,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f73,f50])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f865,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK0))
      | k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0)) ) ),
    inference(resolution,[],[f286,f50])).

fof(f286,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | k4_subset_1(X1,X2,X3) = k3_tarski(k2_tarski(X2,X3))
      | ~ r1_tarski(X3,X1) ) ),
    inference(resolution,[],[f86,f74])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f77,f62])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f290,plain,(
    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f288,f49])).

fof(f288,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f55,f50])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) != X1
      | v4_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f98,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f51,f94,f90])).

fof(f51,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f97,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f52,f94,f90])).

fof(f52,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:50:12 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.21/0.50  % (31265)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.50  % (31266)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (31257)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (31256)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (31262)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (31273)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (31253)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (31252)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (31254)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (31264)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (31263)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (31259)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (31261)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (31260)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (31281)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (31255)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (31272)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (31277)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (31264)Refutation not found, incomplete strategy% (31264)------------------------------
% 0.21/0.55  % (31264)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (31264)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (31264)Memory used [KB]: 10746
% 0.21/0.55  % (31264)Time elapsed: 0.154 s
% 0.21/0.55  % (31264)------------------------------
% 0.21/0.55  % (31264)------------------------------
% 0.21/0.55  % (31278)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (31275)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.56  % (31253)Refutation not found, incomplete strategy% (31253)------------------------------
% 0.21/0.56  % (31253)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (31253)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (31271)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.56  % (31253)Memory used [KB]: 1791
% 0.21/0.56  % (31253)Time elapsed: 0.149 s
% 0.21/0.56  % (31253)------------------------------
% 0.21/0.56  % (31253)------------------------------
% 0.21/0.56  % (31268)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.58/0.57  % (31274)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.58/0.57  % (31267)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.58/0.57  % (31279)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.58/0.57  % (31276)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.58/0.57  % (31258)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.58/0.58  % (31270)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.68/0.58  % (31280)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.68/0.59  % (31269)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.68/0.63  % (31278)Refutation not found, incomplete strategy% (31278)------------------------------
% 1.68/0.63  % (31278)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.63  % (31278)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.63  
% 1.68/0.63  % (31278)Memory used [KB]: 6652
% 1.68/0.63  % (31278)Time elapsed: 0.215 s
% 1.68/0.63  % (31278)------------------------------
% 1.68/0.63  % (31278)------------------------------
% 2.69/0.73  % (31258)Refutation found. Thanks to Tanya!
% 2.69/0.73  % SZS status Theorem for theBenchmark
% 2.69/0.73  % SZS output start Proof for theBenchmark
% 2.69/0.73  fof(f1964,plain,(
% 2.69/0.73    $false),
% 2.69/0.73    inference(avatar_sat_refutation,[],[f97,f98,f1919,f1930,f1963])).
% 2.69/0.73  fof(f1963,plain,(
% 2.69/0.73    spl2_2 | ~spl2_44),
% 2.69/0.73    inference(avatar_contradiction_clause,[],[f1962])).
% 2.69/0.73  fof(f1962,plain,(
% 2.69/0.73    $false | (spl2_2 | ~spl2_44)),
% 2.69/0.73    inference(subsumption_resolution,[],[f1961,f96])).
% 2.69/0.73  fof(f96,plain,(
% 2.69/0.73    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | spl2_2),
% 2.69/0.73    inference(avatar_component_clause,[],[f94])).
% 2.69/0.73  fof(f94,plain,(
% 2.69/0.73    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 2.69/0.73    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 2.69/0.73  fof(f1961,plain,(
% 2.69/0.73    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_44),
% 2.69/0.73    inference(forward_demodulation,[],[f326,f1927])).
% 2.69/0.73  fof(f1927,plain,(
% 2.69/0.73    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_44),
% 2.69/0.73    inference(avatar_component_clause,[],[f1925])).
% 2.69/0.73  fof(f1925,plain,(
% 2.69/0.73    spl2_44 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 2.69/0.73    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 2.69/0.73  fof(f326,plain,(
% 2.69/0.73    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 2.69/0.73    inference(subsumption_resolution,[],[f324,f49])).
% 2.69/0.73  fof(f49,plain,(
% 2.69/0.73    l1_pre_topc(sK0)),
% 2.69/0.73    inference(cnf_transformation,[],[f44])).
% 2.69/0.73  fof(f44,plain,(
% 2.69/0.73    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.69/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).
% 2.69/0.74  fof(f42,plain,(
% 2.69/0.74    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.69/0.74    introduced(choice_axiom,[])).
% 2.69/0.74  fof(f43,plain,(
% 2.69/0.74    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.69/0.74    introduced(choice_axiom,[])).
% 2.69/0.74  fof(f41,plain,(
% 2.69/0.74    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.69/0.74    inference(flattening,[],[f40])).
% 2.69/0.74  fof(f40,plain,(
% 2.69/0.74    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.69/0.74    inference(nnf_transformation,[],[f25])).
% 2.69/0.74  fof(f25,plain,(
% 2.69/0.74    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.69/0.74    inference(flattening,[],[f24])).
% 2.69/0.74  fof(f24,plain,(
% 2.69/0.74    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.69/0.74    inference(ennf_transformation,[],[f23])).
% 2.69/0.74  fof(f23,negated_conjecture,(
% 2.69/0.74    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.69/0.74    inference(negated_conjecture,[],[f22])).
% 2.69/0.74  fof(f22,conjecture,(
% 2.69/0.74    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.69/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).
% 2.69/0.74  fof(f324,plain,(
% 2.69/0.74    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 2.69/0.74    inference(resolution,[],[f56,f50])).
% 2.69/0.74  fof(f50,plain,(
% 2.69/0.74    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.69/0.74    inference(cnf_transformation,[],[f44])).
% 2.69/0.74  fof(f56,plain,(
% 2.69/0.74    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 2.69/0.74    inference(cnf_transformation,[],[f27])).
% 2.69/0.74  fof(f27,plain,(
% 2.69/0.74    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.69/0.74    inference(ennf_transformation,[],[f20])).
% 2.69/0.74  fof(f20,axiom,(
% 2.69/0.74    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 2.69/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 2.69/0.74  fof(f1930,plain,(
% 2.69/0.74    spl2_44 | ~spl2_1),
% 2.69/0.74    inference(avatar_split_clause,[],[f1929,f90,f1925])).
% 2.69/0.74  fof(f90,plain,(
% 2.69/0.74    spl2_1 <=> v4_pre_topc(sK1,sK0)),
% 2.69/0.74    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 2.69/0.74  fof(f1929,plain,(
% 2.69/0.74    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1)),
% 2.69/0.74    inference(subsumption_resolution,[],[f252,f49])).
% 2.69/0.74  fof(f252,plain,(
% 2.69/0.74    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 2.69/0.74    inference(resolution,[],[f57,f50])).
% 2.69/0.74  fof(f57,plain,(
% 2.69/0.74    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 2.69/0.74    inference(cnf_transformation,[],[f29])).
% 2.69/0.74  fof(f29,plain,(
% 2.69/0.74    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.69/0.74    inference(flattening,[],[f28])).
% 2.69/0.74  fof(f28,plain,(
% 2.69/0.74    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.69/0.74    inference(ennf_transformation,[],[f18])).
% 2.69/0.74  fof(f18,axiom,(
% 2.69/0.74    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.69/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 2.69/0.74  fof(f1919,plain,(
% 2.69/0.74    spl2_1 | ~spl2_2),
% 2.69/0.74    inference(avatar_contradiction_clause,[],[f1918])).
% 2.69/0.74  fof(f1918,plain,(
% 2.69/0.74    $false | (spl2_1 | ~spl2_2)),
% 2.69/0.74    inference(subsumption_resolution,[],[f1917,f49])).
% 2.69/0.74  fof(f1917,plain,(
% 2.69/0.74    ~l1_pre_topc(sK0) | (spl2_1 | ~spl2_2)),
% 2.69/0.74    inference(subsumption_resolution,[],[f1916,f50])).
% 2.69/0.74  fof(f1916,plain,(
% 2.69/0.74    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl2_1 | ~spl2_2)),
% 2.69/0.74    inference(subsumption_resolution,[],[f1915,f48])).
% 2.69/0.74  fof(f48,plain,(
% 2.69/0.74    v2_pre_topc(sK0)),
% 2.69/0.74    inference(cnf_transformation,[],[f44])).
% 2.69/0.74  fof(f1915,plain,(
% 2.69/0.74    ~v2_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl2_1 | ~spl2_2)),
% 2.69/0.74    inference(subsumption_resolution,[],[f1903,f92])).
% 2.69/0.74  fof(f92,plain,(
% 2.69/0.74    ~v4_pre_topc(sK1,sK0) | spl2_1),
% 2.69/0.74    inference(avatar_component_clause,[],[f90])).
% 2.69/0.74  fof(f1903,plain,(
% 2.69/0.74    v4_pre_topc(sK1,sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_2),
% 2.69/0.74    inference(trivial_inequality_removal,[],[f1902])).
% 2.69/0.74  fof(f1902,plain,(
% 2.69/0.74    sK1 != sK1 | v4_pre_topc(sK1,sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_2),
% 2.69/0.74    inference(superposition,[],[f58,f1896])).
% 2.69/0.74  fof(f1896,plain,(
% 2.69/0.74    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_2),
% 2.69/0.74    inference(backward_demodulation,[],[f290,f1892])).
% 2.69/0.74  fof(f1892,plain,(
% 2.69/0.74    sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_2),
% 2.69/0.74    inference(forward_demodulation,[],[f1880,f1032])).
% 2.69/0.74  fof(f1032,plain,(
% 2.69/0.74    sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_2),
% 2.69/0.74    inference(forward_demodulation,[],[f1031,f139])).
% 2.69/0.74  fof(f139,plain,(
% 2.69/0.74    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.69/0.74    inference(backward_demodulation,[],[f105,f137])).
% 2.69/0.74  fof(f137,plain,(
% 2.69/0.74    ( ! [X2] : (k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X2))) )),
% 2.69/0.74    inference(resolution,[],[f120,f80])).
% 2.69/0.74  fof(f80,plain,(
% 2.69/0.74    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 2.69/0.74    inference(definition_unfolding,[],[f59,f63])).
% 2.69/0.74  fof(f63,plain,(
% 2.69/0.74    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.69/0.74    inference(cnf_transformation,[],[f16])).
% 2.69/0.74  fof(f16,axiom,(
% 2.69/0.74    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.69/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.69/0.74  fof(f59,plain,(
% 2.69/0.74    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.69/0.74    inference(cnf_transformation,[],[f3])).
% 2.69/0.74  fof(f3,axiom,(
% 2.69/0.74    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.69/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.69/0.74  fof(f120,plain,(
% 2.69/0.74    ( ! [X5] : (~r1_tarski(X5,k1_xboole_0) | k1_xboole_0 = X5) )),
% 2.69/0.74    inference(resolution,[],[f72,f53])).
% 2.69/0.74  fof(f53,plain,(
% 2.69/0.74    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.69/0.74    inference(cnf_transformation,[],[f6])).
% 2.69/0.74  fof(f6,axiom,(
% 2.69/0.74    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.69/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.69/0.74  fof(f72,plain,(
% 2.69/0.74    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.69/0.74    inference(cnf_transformation,[],[f46])).
% 2.69/0.74  fof(f46,plain,(
% 2.69/0.74    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.69/0.74    inference(flattening,[],[f45])).
% 2.69/0.74  fof(f45,plain,(
% 2.69/0.74    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.69/0.74    inference(nnf_transformation,[],[f1])).
% 2.69/0.74  fof(f1,axiom,(
% 2.69/0.74    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.69/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.69/0.74  fof(f105,plain,(
% 2.69/0.74    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(k1_xboole_0,X0))) = X0) )),
% 2.69/0.74    inference(superposition,[],[f79,f61])).
% 2.69/0.74  fof(f61,plain,(
% 2.69/0.74    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.69/0.74    inference(cnf_transformation,[],[f10])).
% 2.69/0.74  fof(f10,axiom,(
% 2.69/0.74    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.69/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.69/0.74  fof(f79,plain,(
% 2.69/0.74    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 2.69/0.74    inference(definition_unfolding,[],[f54,f78])).
% 2.69/0.74  fof(f78,plain,(
% 2.69/0.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.69/0.74    inference(definition_unfolding,[],[f65,f63])).
% 2.69/0.74  fof(f65,plain,(
% 2.69/0.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.69/0.74    inference(cnf_transformation,[],[f2])).
% 2.69/0.74  fof(f2,axiom,(
% 2.69/0.74    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.69/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.69/0.74  fof(f54,plain,(
% 2.69/0.74    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.69/0.74    inference(cnf_transformation,[],[f8])).
% 2.69/0.74  fof(f8,axiom,(
% 2.69/0.74    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.69/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.69/0.74  fof(f1031,plain,(
% 2.69/0.74    k5_xboole_0(sK1,k1_xboole_0) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_2),
% 2.69/0.74    inference(forward_demodulation,[],[f1017,f700])).
% 2.69/0.74  fof(f700,plain,(
% 2.69/0.74    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.69/0.74    inference(forward_demodulation,[],[f690,f697])).
% 2.69/0.74  fof(f697,plain,(
% 2.69/0.74    ( ! [X6] : (k1_xboole_0 = k3_subset_1(X6,X6)) )),
% 2.69/0.74    inference(backward_demodulation,[],[f470,f692])).
% 2.69/0.74  fof(f692,plain,(
% 2.69/0.74    ( ! [X6] : (k3_subset_1(X6,k1_xboole_0) = X6) )),
% 2.69/0.74    inference(forward_demodulation,[],[f691,f139])).
% 2.69/0.74  fof(f691,plain,(
% 2.69/0.74    ( ! [X6] : (k3_subset_1(X6,k1_xboole_0) = k5_xboole_0(X6,k1_xboole_0)) )),
% 2.69/0.74    inference(forward_demodulation,[],[f667,f138])).
% 2.69/0.74  fof(f138,plain,(
% 2.69/0.74    ( ! [X3] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X3,k1_xboole_0))) )),
% 2.69/0.74    inference(resolution,[],[f120,f99])).
% 2.69/0.74  fof(f99,plain,(
% 2.69/0.74    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0)) )),
% 2.69/0.74    inference(superposition,[],[f80,f61])).
% 2.69/0.74  fof(f667,plain,(
% 2.69/0.74    ( ! [X6] : (k3_subset_1(X6,k1_xboole_0) = k5_xboole_0(X6,k1_setfam_1(k2_tarski(X6,k1_xboole_0)))) )),
% 2.69/0.74    inference(resolution,[],[f238,f53])).
% 2.69/0.74  fof(f238,plain,(
% 2.69/0.74    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.69/0.74    inference(resolution,[],[f84,f74])).
% 2.69/0.74  fof(f74,plain,(
% 2.69/0.74    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.69/0.74    inference(cnf_transformation,[],[f47])).
% 2.69/0.74  fof(f47,plain,(
% 2.69/0.74    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.69/0.74    inference(nnf_transformation,[],[f17])).
% 2.69/0.74  fof(f17,axiom,(
% 2.69/0.74    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.69/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.69/0.74  fof(f84,plain,(
% 2.69/0.74    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.69/0.74    inference(definition_unfolding,[],[f67,f78])).
% 2.69/0.74  fof(f67,plain,(
% 2.69/0.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.69/0.74    inference(cnf_transformation,[],[f31])).
% 2.69/0.74  fof(f31,plain,(
% 2.69/0.74    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.69/0.74    inference(ennf_transformation,[],[f12])).
% 2.69/0.74  fof(f12,axiom,(
% 2.69/0.74    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.69/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 2.69/0.74  fof(f470,plain,(
% 2.69/0.74    ( ! [X6] : (k1_xboole_0 = k3_subset_1(X6,k3_subset_1(X6,k1_xboole_0))) )),
% 2.69/0.74    inference(resolution,[],[f175,f53])).
% 2.69/0.74  fof(f175,plain,(
% 2.69/0.74    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 2.69/0.74    inference(resolution,[],[f68,f74])).
% 2.69/0.74  fof(f68,plain,(
% 2.69/0.74    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 2.69/0.74    inference(cnf_transformation,[],[f32])).
% 2.69/0.74  fof(f32,plain,(
% 2.69/0.74    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.69/0.74    inference(ennf_transformation,[],[f13])).
% 2.69/0.74  fof(f13,axiom,(
% 2.69/0.74    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.69/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.69/0.74  fof(f690,plain,(
% 2.69/0.74    ( ! [X0] : (k5_xboole_0(X0,X0) = k3_subset_1(X0,X0)) )),
% 2.69/0.74    inference(forward_demodulation,[],[f663,f156])).
% 2.69/0.74  fof(f156,plain,(
% 2.69/0.74    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,X0)) = X0) )),
% 2.69/0.74    inference(resolution,[],[f83,f87])).
% 2.69/0.74  fof(f87,plain,(
% 2.69/0.74    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.69/0.74    inference(equality_resolution,[],[f71])).
% 2.69/0.74  fof(f71,plain,(
% 2.69/0.74    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.69/0.74    inference(cnf_transformation,[],[f46])).
% 2.69/0.74  fof(f83,plain,(
% 2.69/0.74    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 2.69/0.74    inference(definition_unfolding,[],[f66,f63])).
% 2.69/0.74  fof(f66,plain,(
% 2.69/0.74    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.69/0.74    inference(cnf_transformation,[],[f30])).
% 2.69/0.74  fof(f30,plain,(
% 2.69/0.74    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.69/0.74    inference(ennf_transformation,[],[f5])).
% 2.69/0.74  fof(f5,axiom,(
% 2.69/0.74    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.69/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.69/0.74  fof(f663,plain,(
% 2.69/0.74    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0))) = k3_subset_1(X0,X0)) )),
% 2.69/0.74    inference(resolution,[],[f238,f87])).
% 2.69/0.74  fof(f1017,plain,(
% 2.69/0.74    k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))) | ~spl2_2),
% 2.69/0.74    inference(superposition,[],[f202,f442])).
% 2.69/0.74  fof(f442,plain,(
% 2.69/0.74    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_2),
% 2.69/0.74    inference(forward_demodulation,[],[f437,f61])).
% 2.69/0.74  fof(f437,plain,(
% 2.69/0.74    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) | ~spl2_2),
% 2.69/0.74    inference(resolution,[],[f431,f83])).
% 2.69/0.74  fof(f431,plain,(
% 2.69/0.74    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_2),
% 2.69/0.74    inference(superposition,[],[f423,f95])).
% 2.69/0.74  fof(f95,plain,(
% 2.69/0.74    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_2),
% 2.69/0.74    inference(avatar_component_clause,[],[f94])).
% 2.69/0.74  fof(f423,plain,(
% 2.69/0.74    ( ! [X1] : (r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X1),sK1)) )),
% 2.69/0.74    inference(superposition,[],[f81,f258])).
% 2.69/0.74  fof(f258,plain,(
% 2.69/0.74    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))) )),
% 2.69/0.74    inference(resolution,[],[f85,f50])).
% 2.69/0.74  fof(f85,plain,(
% 2.69/0.74    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) )),
% 2.69/0.74    inference(definition_unfolding,[],[f75,f78])).
% 2.69/0.74  fof(f75,plain,(
% 2.69/0.74    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.69/0.74    inference(cnf_transformation,[],[f35])).
% 2.69/0.74  fof(f35,plain,(
% 2.69/0.74    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.69/0.74    inference(ennf_transformation,[],[f15])).
% 2.69/0.74  fof(f15,axiom,(
% 2.69/0.74    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.69/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.69/0.74  fof(f81,plain,(
% 2.69/0.74    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 2.69/0.74    inference(definition_unfolding,[],[f60,f78])).
% 2.69/0.74  fof(f60,plain,(
% 2.69/0.74    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.69/0.74    inference(cnf_transformation,[],[f7])).
% 2.69/0.74  fof(f7,axiom,(
% 2.69/0.74    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.69/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.69/0.74  fof(f202,plain,(
% 2.69/0.74    ( ! [X0,X1] : (k3_tarski(k2_tarski(X1,X0)) = k5_xboole_0(X1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))))) )),
% 2.69/0.74    inference(superposition,[],[f82,f61])).
% 2.69/0.74  fof(f82,plain,(
% 2.69/0.74    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))) )),
% 2.69/0.74    inference(definition_unfolding,[],[f64,f62,f78])).
% 2.69/0.74  fof(f62,plain,(
% 2.69/0.74    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.69/0.74    inference(cnf_transformation,[],[f11])).
% 2.69/0.74  fof(f11,axiom,(
% 2.69/0.74    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.69/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.69/0.74  fof(f64,plain,(
% 2.69/0.74    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.69/0.74    inference(cnf_transformation,[],[f9])).
% 2.69/0.74  fof(f9,axiom,(
% 2.69/0.74    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.69/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.69/0.74  fof(f1880,plain,(
% 2.69/0.74    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_2),
% 2.69/0.74    inference(resolution,[],[f865,f441])).
% 2.69/0.74  fof(f441,plain,(
% 2.69/0.74    r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) | ~spl2_2),
% 2.69/0.74    inference(subsumption_resolution,[],[f436,f87])).
% 2.69/0.74  fof(f436,plain,(
% 2.69/0.74    r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) | ~r1_tarski(sK1,sK1) | ~spl2_2),
% 2.69/0.74    inference(resolution,[],[f431,f168])).
% 2.69/0.74  fof(f168,plain,(
% 2.69/0.74    ( ! [X2,X1] : (~r1_tarski(X2,X1) | r1_tarski(X2,u1_struct_0(sK0)) | ~r1_tarski(X1,sK1)) )),
% 2.69/0.74    inference(resolution,[],[f152,f76])).
% 2.69/0.74  fof(f76,plain,(
% 2.69/0.74    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.69/0.74    inference(cnf_transformation,[],[f37])).
% 2.69/0.74  fof(f37,plain,(
% 2.69/0.74    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.69/0.74    inference(flattening,[],[f36])).
% 2.69/0.74  fof(f36,plain,(
% 2.69/0.74    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.69/0.74    inference(ennf_transformation,[],[f4])).
% 2.69/0.74  fof(f4,axiom,(
% 2.69/0.74    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.69/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.69/0.74  fof(f152,plain,(
% 2.69/0.74    ( ! [X13] : (r1_tarski(X13,u1_struct_0(sK0)) | ~r1_tarski(X13,sK1)) )),
% 2.69/0.74    inference(resolution,[],[f76,f101])).
% 2.69/0.74  fof(f101,plain,(
% 2.69/0.74    r1_tarski(sK1,u1_struct_0(sK0))),
% 2.69/0.74    inference(resolution,[],[f73,f50])).
% 2.69/0.74  fof(f73,plain,(
% 2.69/0.74    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.69/0.74    inference(cnf_transformation,[],[f47])).
% 2.69/0.74  fof(f865,plain,(
% 2.69/0.74    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))) )),
% 2.69/0.74    inference(resolution,[],[f286,f50])).
% 2.69/0.74  fof(f286,plain,(
% 2.69/0.74    ( ! [X2,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X1)) | k4_subset_1(X1,X2,X3) = k3_tarski(k2_tarski(X2,X3)) | ~r1_tarski(X3,X1)) )),
% 2.69/0.74    inference(resolution,[],[f86,f74])).
% 2.69/0.74  fof(f86,plain,(
% 2.69/0.74    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.69/0.74    inference(definition_unfolding,[],[f77,f62])).
% 2.69/0.74  fof(f77,plain,(
% 2.69/0.74    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.69/0.74    inference(cnf_transformation,[],[f39])).
% 2.69/0.74  fof(f39,plain,(
% 2.69/0.74    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.69/0.74    inference(flattening,[],[f38])).
% 2.69/0.74  fof(f38,plain,(
% 2.69/0.74    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.69/0.74    inference(ennf_transformation,[],[f14])).
% 2.69/0.74  fof(f14,axiom,(
% 2.69/0.74    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 2.69/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.69/0.74  fof(f290,plain,(
% 2.69/0.74    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.69/0.74    inference(subsumption_resolution,[],[f288,f49])).
% 2.69/0.74  fof(f288,plain,(
% 2.69/0.74    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 2.69/0.74    inference(resolution,[],[f55,f50])).
% 2.69/0.74  fof(f55,plain,(
% 2.69/0.74    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 2.69/0.74    inference(cnf_transformation,[],[f26])).
% 2.69/0.74  fof(f26,plain,(
% 2.69/0.74    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.69/0.74    inference(ennf_transformation,[],[f21])).
% 2.69/0.74  fof(f21,axiom,(
% 2.69/0.74    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.69/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 2.69/0.74  fof(f58,plain,(
% 2.69/0.74    ( ! [X0,X1] : (k2_pre_topc(X0,X1) != X1 | v4_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.69/0.74    inference(cnf_transformation,[],[f29])).
% 2.69/0.74  fof(f98,plain,(
% 2.69/0.74    spl2_1 | spl2_2),
% 2.69/0.74    inference(avatar_split_clause,[],[f51,f94,f90])).
% 2.69/0.74  fof(f51,plain,(
% 2.69/0.74    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 2.69/0.74    inference(cnf_transformation,[],[f44])).
% 2.69/0.74  fof(f97,plain,(
% 2.69/0.74    ~spl2_1 | ~spl2_2),
% 2.69/0.74    inference(avatar_split_clause,[],[f52,f94,f90])).
% 2.69/0.74  fof(f52,plain,(
% 2.69/0.74    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 2.69/0.74    inference(cnf_transformation,[],[f44])).
% 2.69/0.74  % SZS output end Proof for theBenchmark
% 2.69/0.74  % (31258)------------------------------
% 2.69/0.74  % (31258)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.69/0.74  % (31258)Termination reason: Refutation
% 2.69/0.74  
% 2.69/0.74  % (31258)Memory used [KB]: 12025
% 2.69/0.74  % (31258)Time elapsed: 0.254 s
% 2.69/0.74  % (31258)------------------------------
% 2.69/0.74  % (31258)------------------------------
% 2.69/0.74  % (31304)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.69/0.75  % (31251)Success in time 0.389 s
%------------------------------------------------------------------------------
