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
% DateTime   : Thu Dec  3 13:12:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 613 expanded)
%              Number of leaves         :   22 ( 176 expanded)
%              Depth                    :   26
%              Number of atoms          :  329 (1871 expanded)
%              Number of equality atoms :  113 ( 626 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1979,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f89,f1922,f1933,f1978])).

fof(f1978,plain,
    ( spl2_2
    | ~ spl2_27 ),
    inference(avatar_contradiction_clause,[],[f1977])).

fof(f1977,plain,
    ( $false
    | spl2_2
    | ~ spl2_27 ),
    inference(subsumption_resolution,[],[f1976,f87])).

fof(f87,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f1976,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_27 ),
    inference(forward_demodulation,[],[f313,f1930])).

fof(f1930,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f1928])).

fof(f1928,plain,
    ( spl2_27
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f313,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f309,f47])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f41,f40])).

fof(f40,plain,
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

fof(f41,plain,
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

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(f309,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f53,f48])).

fof(f48,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f1933,plain,
    ( spl2_27
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f1932,f81,f1928])).

fof(f81,plain,
    ( spl2_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f1932,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f239,f47])).

fof(f239,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f54,f48])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f1922,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f1921])).

fof(f1921,plain,
    ( $false
    | spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f1920,f47])).

fof(f1920,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f1919,f48])).

fof(f1919,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f1918,f46])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f1918,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f1908,f83])).

fof(f83,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f1908,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(trivial_inequality_removal,[],[f1907])).

fof(f1907,plain,
    ( sK1 != sK1
    | v4_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(superposition,[],[f55,f1901])).

fof(f1901,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f1316,f1486])).

fof(f1486,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(superposition,[],[f1239,f86])).

fof(f86,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f1239,plain,(
    ! [X5] : sK1 = k2_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X5)) ),
    inference(forward_demodulation,[],[f1238,f51])).

fof(f51,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f1238,plain,(
    ! [X5] : k2_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X5)) ),
    inference(forward_demodulation,[],[f1230,f472])).

fof(f472,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f437,f440])).

fof(f440,plain,(
    ! [X8] : k1_xboole_0 = k3_subset_1(X8,X8) ),
    inference(backward_demodulation,[],[f380,f438])).

fof(f438,plain,(
    ! [X9] : k3_subset_1(X9,k1_xboole_0) = X9 ),
    inference(forward_demodulation,[],[f427,f141])).

fof(f141,plain,(
    ! [X6] : k5_xboole_0(X6,k3_xboole_0(X6,k1_xboole_0)) = X6 ),
    inference(forward_demodulation,[],[f138,f90])).

fof(f90,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f57,f51])).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f138,plain,(
    ! [X6] : k5_xboole_0(X6,k3_xboole_0(X6,k1_xboole_0)) = k2_xboole_0(k1_xboole_0,X6) ),
    inference(superposition,[],[f74,f90])).

fof(f74,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f59,f58])).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f427,plain,(
    ! [X9] : k5_xboole_0(X9,k3_xboole_0(X9,k1_xboole_0)) = k3_subset_1(X9,k1_xboole_0) ),
    inference(resolution,[],[f168,f160])).

fof(f160,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(superposition,[],[f148,f51])).

fof(f148,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(resolution,[],[f77,f73])).

fof(f73,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f56,f58])).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f71,f58])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f168,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(resolution,[],[f75,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f61,f58])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f380,plain,(
    ! [X8] : k1_xboole_0 = k3_subset_1(X8,k3_subset_1(X8,k1_xboole_0)) ),
    inference(resolution,[],[f131,f160])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(resolution,[],[f62,f69])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f437,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f418,f100])).

fof(f100,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f60,f78])).

fof(f78,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f418,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_subset_1(X0,X0) ),
    inference(resolution,[],[f168,f78])).

fof(f1230,plain,(
    ! [X5] : k2_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X5)) = k2_xboole_0(sK1,k5_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,X5),k7_subset_1(u1_struct_0(sK0),sK1,X5))) ),
    inference(superposition,[],[f74,f454])).

fof(f454,plain,(
    ! [X1] : k7_subset_1(u1_struct_0(sK0),sK1,X1) = k3_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,X1),sK1) ),
    inference(superposition,[],[f102,f213])).

fof(f213,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
    inference(resolution,[],[f76,f48])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f70,f58])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f102,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(resolution,[],[f60,f73])).

fof(f1316,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f1306,f286])).

fof(f286,plain,(
    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f282,f47])).

fof(f282,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f52,f48])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f1306,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(resolution,[],[f1297,f601])).

fof(f601,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK0))
      | k2_xboole_0(sK1,X0) = k4_subset_1(u1_struct_0(sK0),sK1,X0) ) ),
    inference(resolution,[],[f245,f48])).

fof(f245,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X3))
      | k2_xboole_0(X1,X2) = k4_subset_1(X3,X1,X2)
      | ~ r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f72,f69])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f1297,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl2_2 ),
    inference(superposition,[],[f1277,f572])).

fof(f572,plain,(
    u1_struct_0(sK0) = k2_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(backward_demodulation,[],[f339,f490])).

fof(f490,plain,(
    u1_struct_0(sK0) = k2_xboole_0(sK1,u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f478,f51])).

fof(f478,plain,(
    k2_xboole_0(sK1,u1_struct_0(sK0)) = k2_xboole_0(u1_struct_0(sK0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f140,f472])).

fof(f140,plain,(
    k2_xboole_0(u1_struct_0(sK0),k5_xboole_0(sK1,sK1)) = k2_xboole_0(sK1,u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f134,f57])).

fof(f134,plain,(
    k2_xboole_0(u1_struct_0(sK0),sK1) = k2_xboole_0(u1_struct_0(sK0),k5_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f74,f101])).

fof(f101,plain,(
    sK1 = k3_xboole_0(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f60,f98])).

fof(f98,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f68,f48])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f339,plain,(
    k2_xboole_0(sK1,u1_struct_0(sK0)) = k2_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(superposition,[],[f74,f167])).

fof(f167,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k3_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f75,f48])).

fof(f1277,plain,
    ( ! [X10] : r1_tarski(k2_tops_1(sK0,sK1),k2_xboole_0(sK1,X10))
    | ~ spl2_2 ),
    inference(superposition,[],[f1237,f86])).

fof(f1237,plain,(
    ! [X4,X3] : r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X3),k2_xboole_0(sK1,X4)) ),
    inference(subsumption_resolution,[],[f1236,f160])).

fof(f1236,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(k1_xboole_0,X4)
      | r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X3),k2_xboole_0(sK1,X4)) ) ),
    inference(forward_demodulation,[],[f1229,f472])).

fof(f1229,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(k5_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,X3),k7_subset_1(u1_struct_0(sK0),sK1,X3)),X4)
      | r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X3),k2_xboole_0(sK1,X4)) ) ),
    inference(superposition,[],[f77,f454])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) != X1
      | v4_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f89,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f49,f85,f81])).

fof(f49,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f88,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f50,f85,f81])).

fof(f50,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:04:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (3553)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.51  % (3545)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.51  % (3541)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (3549)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (3547)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.52  % (3536)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (3530)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (3558)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (3539)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (3537)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (3550)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (3542)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (3533)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (3556)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (3532)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (3534)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (3529)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (3538)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (3535)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (3557)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (3557)Refutation not found, incomplete strategy% (3557)------------------------------
% 0.21/0.54  % (3557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3557)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3557)Memory used [KB]: 10746
% 0.21/0.54  % (3557)Time elapsed: 0.131 s
% 0.21/0.54  % (3557)------------------------------
% 0.21/0.54  % (3557)------------------------------
% 0.21/0.54  % (3531)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.55  % (3548)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (3540)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (3528)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.55  % (3546)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.56  % (3543)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.56  % (3551)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.56  % (3544)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.56  % (3554)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (3544)Refutation not found, incomplete strategy% (3544)------------------------------
% 0.21/0.56  % (3544)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (3544)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (3544)Memory used [KB]: 10618
% 0.21/0.56  % (3544)Time elapsed: 0.152 s
% 0.21/0.56  % (3544)------------------------------
% 0.21/0.56  % (3544)------------------------------
% 0.21/0.56  % (3552)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.57  % (3538)Refutation not found, incomplete strategy% (3538)------------------------------
% 0.21/0.57  % (3538)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (3538)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (3538)Memory used [KB]: 10874
% 0.21/0.57  % (3538)Time elapsed: 0.156 s
% 0.21/0.57  % (3538)------------------------------
% 0.21/0.57  % (3538)------------------------------
% 0.21/0.63  % (3534)Refutation found. Thanks to Tanya!
% 0.21/0.63  % SZS status Theorem for theBenchmark
% 0.21/0.65  % SZS output start Proof for theBenchmark
% 0.21/0.65  fof(f1979,plain,(
% 0.21/0.65    $false),
% 0.21/0.65    inference(avatar_sat_refutation,[],[f88,f89,f1922,f1933,f1978])).
% 0.21/0.65  fof(f1978,plain,(
% 0.21/0.65    spl2_2 | ~spl2_27),
% 0.21/0.65    inference(avatar_contradiction_clause,[],[f1977])).
% 0.21/0.65  fof(f1977,plain,(
% 0.21/0.65    $false | (spl2_2 | ~spl2_27)),
% 0.21/0.65    inference(subsumption_resolution,[],[f1976,f87])).
% 0.21/0.65  fof(f87,plain,(
% 0.21/0.65    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | spl2_2),
% 0.21/0.65    inference(avatar_component_clause,[],[f85])).
% 0.21/0.65  fof(f85,plain,(
% 0.21/0.65    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 0.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.65  fof(f1976,plain,(
% 0.21/0.65    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_27),
% 0.21/0.65    inference(forward_demodulation,[],[f313,f1930])).
% 0.21/0.65  fof(f1930,plain,(
% 0.21/0.65    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_27),
% 0.21/0.65    inference(avatar_component_clause,[],[f1928])).
% 0.21/0.65  fof(f1928,plain,(
% 0.21/0.65    spl2_27 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.21/0.65  fof(f313,plain,(
% 0.21/0.65    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 0.21/0.65    inference(subsumption_resolution,[],[f309,f47])).
% 0.21/0.65  fof(f47,plain,(
% 0.21/0.65    l1_pre_topc(sK0)),
% 0.21/0.65    inference(cnf_transformation,[],[f42])).
% 0.21/0.65  fof(f42,plain,(
% 0.21/0.65    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f41,f40])).
% 0.21/0.65  fof(f40,plain,(
% 0.21/0.65    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.65    introduced(choice_axiom,[])).
% 0.21/0.65  fof(f41,plain,(
% 0.21/0.65    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.65    introduced(choice_axiom,[])).
% 0.21/0.65  fof(f39,plain,(
% 0.21/0.65    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.65    inference(flattening,[],[f38])).
% 0.21/0.65  fof(f38,plain,(
% 0.21/0.65    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.65    inference(nnf_transformation,[],[f22])).
% 0.21/0.65  fof(f22,plain,(
% 0.21/0.65    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.65    inference(flattening,[],[f21])).
% 0.21/0.65  fof(f21,plain,(
% 0.21/0.65    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.65    inference(ennf_transformation,[],[f20])).
% 0.21/0.65  fof(f20,negated_conjecture,(
% 0.21/0.65    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.21/0.65    inference(negated_conjecture,[],[f19])).
% 0.21/0.65  fof(f19,conjecture,(
% 0.21/0.65    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).
% 0.21/0.65  fof(f309,plain,(
% 0.21/0.65    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.21/0.65    inference(resolution,[],[f53,f48])).
% 0.21/0.65  fof(f48,plain,(
% 0.21/0.65    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.65    inference(cnf_transformation,[],[f42])).
% 0.21/0.65  fof(f53,plain,(
% 0.21/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 0.21/0.65    inference(cnf_transformation,[],[f24])).
% 0.21/0.65  fof(f24,plain,(
% 0.21/0.65    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.65    inference(ennf_transformation,[],[f17])).
% 0.21/0.65  fof(f17,axiom,(
% 0.21/0.65    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 0.21/0.65  fof(f1933,plain,(
% 0.21/0.65    spl2_27 | ~spl2_1),
% 0.21/0.65    inference(avatar_split_clause,[],[f1932,f81,f1928])).
% 0.21/0.65  fof(f81,plain,(
% 0.21/0.65    spl2_1 <=> v4_pre_topc(sK1,sK0)),
% 0.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.65  fof(f1932,plain,(
% 0.21/0.65    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1)),
% 0.21/0.65    inference(subsumption_resolution,[],[f239,f47])).
% 0.21/0.65  fof(f239,plain,(
% 0.21/0.65    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 0.21/0.65    inference(resolution,[],[f54,f48])).
% 0.21/0.65  fof(f54,plain,(
% 0.21/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 0.21/0.65    inference(cnf_transformation,[],[f26])).
% 0.21/0.65  fof(f26,plain,(
% 0.21/0.65    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.65    inference(flattening,[],[f25])).
% 0.21/0.65  fof(f25,plain,(
% 0.21/0.65    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.65    inference(ennf_transformation,[],[f14])).
% 0.21/0.65  fof(f14,axiom,(
% 0.21/0.65    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.21/0.65  fof(f1922,plain,(
% 0.21/0.65    spl2_1 | ~spl2_2),
% 0.21/0.65    inference(avatar_contradiction_clause,[],[f1921])).
% 0.21/0.65  fof(f1921,plain,(
% 0.21/0.65    $false | (spl2_1 | ~spl2_2)),
% 0.21/0.65    inference(subsumption_resolution,[],[f1920,f47])).
% 0.21/0.65  fof(f1920,plain,(
% 0.21/0.65    ~l1_pre_topc(sK0) | (spl2_1 | ~spl2_2)),
% 0.21/0.65    inference(subsumption_resolution,[],[f1919,f48])).
% 0.21/0.65  fof(f1919,plain,(
% 0.21/0.65    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl2_1 | ~spl2_2)),
% 0.21/0.65    inference(subsumption_resolution,[],[f1918,f46])).
% 0.21/0.65  fof(f46,plain,(
% 0.21/0.65    v2_pre_topc(sK0)),
% 0.21/0.65    inference(cnf_transformation,[],[f42])).
% 0.21/0.65  fof(f1918,plain,(
% 0.21/0.65    ~v2_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl2_1 | ~spl2_2)),
% 0.21/0.65    inference(subsumption_resolution,[],[f1908,f83])).
% 0.21/0.65  fof(f83,plain,(
% 0.21/0.65    ~v4_pre_topc(sK1,sK0) | spl2_1),
% 0.21/0.65    inference(avatar_component_clause,[],[f81])).
% 0.21/0.65  fof(f1908,plain,(
% 0.21/0.65    v4_pre_topc(sK1,sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_2),
% 0.21/0.65    inference(trivial_inequality_removal,[],[f1907])).
% 0.21/0.65  fof(f1907,plain,(
% 0.21/0.65    sK1 != sK1 | v4_pre_topc(sK1,sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_2),
% 0.21/0.65    inference(superposition,[],[f55,f1901])).
% 0.21/0.65  fof(f1901,plain,(
% 0.21/0.65    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_2),
% 0.21/0.65    inference(forward_demodulation,[],[f1316,f1486])).
% 0.21/0.65  fof(f1486,plain,(
% 0.21/0.65    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_2),
% 0.21/0.65    inference(superposition,[],[f1239,f86])).
% 0.21/0.65  fof(f86,plain,(
% 0.21/0.65    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_2),
% 0.21/0.65    inference(avatar_component_clause,[],[f85])).
% 0.21/0.65  fof(f1239,plain,(
% 0.21/0.65    ( ! [X5] : (sK1 = k2_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X5))) )),
% 0.21/0.65    inference(forward_demodulation,[],[f1238,f51])).
% 0.21/0.65  fof(f51,plain,(
% 0.21/0.65    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.65    inference(cnf_transformation,[],[f4])).
% 0.21/0.65  fof(f4,axiom,(
% 0.21/0.65    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.65  fof(f1238,plain,(
% 0.21/0.65    ( ! [X5] : (k2_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X5))) )),
% 0.21/0.65    inference(forward_demodulation,[],[f1230,f472])).
% 0.21/0.65  fof(f472,plain,(
% 0.21/0.65    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.21/0.65    inference(forward_demodulation,[],[f437,f440])).
% 0.21/0.65  fof(f440,plain,(
% 0.21/0.65    ( ! [X8] : (k1_xboole_0 = k3_subset_1(X8,X8)) )),
% 0.21/0.65    inference(backward_demodulation,[],[f380,f438])).
% 0.21/0.65  fof(f438,plain,(
% 0.21/0.65    ( ! [X9] : (k3_subset_1(X9,k1_xboole_0) = X9) )),
% 0.21/0.65    inference(forward_demodulation,[],[f427,f141])).
% 0.21/0.65  fof(f141,plain,(
% 0.21/0.65    ( ! [X6] : (k5_xboole_0(X6,k3_xboole_0(X6,k1_xboole_0)) = X6) )),
% 0.21/0.65    inference(forward_demodulation,[],[f138,f90])).
% 0.21/0.65  fof(f90,plain,(
% 0.21/0.65    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.21/0.65    inference(superposition,[],[f57,f51])).
% 0.21/0.65  fof(f57,plain,(
% 0.21/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.65    inference(cnf_transformation,[],[f1])).
% 0.21/0.65  fof(f1,axiom,(
% 0.21/0.65    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.65  fof(f138,plain,(
% 0.21/0.65    ( ! [X6] : (k5_xboole_0(X6,k3_xboole_0(X6,k1_xboole_0)) = k2_xboole_0(k1_xboole_0,X6)) )),
% 0.21/0.65    inference(superposition,[],[f74,f90])).
% 0.21/0.65  fof(f74,plain,(
% 0.21/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.21/0.65    inference(definition_unfolding,[],[f59,f58])).
% 0.21/0.65  fof(f58,plain,(
% 0.21/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.65    inference(cnf_transformation,[],[f3])).
% 0.21/0.65  fof(f3,axiom,(
% 0.21/0.65    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.65  fof(f59,plain,(
% 0.21/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.65    inference(cnf_transformation,[],[f7])).
% 0.21/0.65  fof(f7,axiom,(
% 0.21/0.65    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.65  fof(f427,plain,(
% 0.21/0.65    ( ! [X9] : (k5_xboole_0(X9,k3_xboole_0(X9,k1_xboole_0)) = k3_subset_1(X9,k1_xboole_0)) )),
% 0.21/0.65    inference(resolution,[],[f168,f160])).
% 0.21/0.65  fof(f160,plain,(
% 0.21/0.65    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.65    inference(superposition,[],[f148,f51])).
% 0.21/0.65  fof(f148,plain,(
% 0.21/0.65    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 0.21/0.65    inference(resolution,[],[f77,f73])).
% 0.21/0.65  fof(f73,plain,(
% 0.21/0.65    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 0.21/0.65    inference(definition_unfolding,[],[f56,f58])).
% 0.21/0.65  fof(f56,plain,(
% 0.21/0.65    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.65    inference(cnf_transformation,[],[f6])).
% 0.21/0.65  fof(f6,axiom,(
% 0.21/0.65    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.65  fof(f77,plain,(
% 0.21/0.65    ( ! [X2,X0,X1] : (~r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.65    inference(definition_unfolding,[],[f71,f58])).
% 0.21/0.66  fof(f71,plain,(
% 0.21/0.66    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 0.21/0.66    inference(cnf_transformation,[],[f35])).
% 0.21/0.66  fof(f35,plain,(
% 0.21/0.66    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.21/0.66    inference(ennf_transformation,[],[f8])).
% 0.21/0.66  fof(f8,axiom,(
% 0.21/0.66    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 0.21/0.66  fof(f168,plain,(
% 0.21/0.66    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 0.21/0.66    inference(resolution,[],[f75,f69])).
% 0.21/0.66  fof(f69,plain,(
% 0.21/0.66    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.66    inference(cnf_transformation,[],[f45])).
% 0.21/0.66  fof(f45,plain,(
% 0.21/0.66    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.66    inference(nnf_transformation,[],[f13])).
% 0.21/0.66  fof(f13,axiom,(
% 0.21/0.66    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.66  fof(f75,plain,(
% 0.21/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 0.21/0.66    inference(definition_unfolding,[],[f61,f58])).
% 0.21/0.66  fof(f61,plain,(
% 0.21/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.66    inference(cnf_transformation,[],[f28])).
% 0.21/0.66  fof(f28,plain,(
% 0.21/0.66    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.66    inference(ennf_transformation,[],[f9])).
% 0.21/0.66  fof(f9,axiom,(
% 0.21/0.66    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.66  fof(f380,plain,(
% 0.21/0.66    ( ! [X8] : (k1_xboole_0 = k3_subset_1(X8,k3_subset_1(X8,k1_xboole_0))) )),
% 0.21/0.66    inference(resolution,[],[f131,f160])).
% 0.21/0.66  fof(f131,plain,(
% 0.21/0.66    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.21/0.66    inference(resolution,[],[f62,f69])).
% 0.21/0.66  fof(f62,plain,(
% 0.21/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.21/0.66    inference(cnf_transformation,[],[f29])).
% 0.21/0.66  fof(f29,plain,(
% 0.21/0.66    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.66    inference(ennf_transformation,[],[f10])).
% 0.21/0.66  fof(f10,axiom,(
% 0.21/0.66    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.66  fof(f437,plain,(
% 0.21/0.66    ( ! [X0] : (k5_xboole_0(X0,X0) = k3_subset_1(X0,X0)) )),
% 0.21/0.66    inference(forward_demodulation,[],[f418,f100])).
% 0.21/0.66  fof(f100,plain,(
% 0.21/0.66    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.21/0.66    inference(resolution,[],[f60,f78])).
% 0.21/0.66  fof(f78,plain,(
% 0.21/0.66    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.66    inference(equality_resolution,[],[f66])).
% 0.21/0.66  fof(f66,plain,(
% 0.21/0.66    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.66    inference(cnf_transformation,[],[f44])).
% 0.21/0.66  fof(f44,plain,(
% 0.21/0.66    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.66    inference(flattening,[],[f43])).
% 0.21/0.66  fof(f43,plain,(
% 0.21/0.66    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.66    inference(nnf_transformation,[],[f2])).
% 0.21/0.66  fof(f2,axiom,(
% 0.21/0.66    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.66  fof(f60,plain,(
% 0.21/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.66    inference(cnf_transformation,[],[f27])).
% 0.21/0.66  fof(f27,plain,(
% 0.21/0.66    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.66    inference(ennf_transformation,[],[f5])).
% 0.21/0.66  fof(f5,axiom,(
% 0.21/0.66    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.66  fof(f418,plain,(
% 0.21/0.66    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_subset_1(X0,X0)) )),
% 0.21/0.66    inference(resolution,[],[f168,f78])).
% 0.21/0.66  fof(f1230,plain,(
% 0.21/0.66    ( ! [X5] : (k2_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X5)) = k2_xboole_0(sK1,k5_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,X5),k7_subset_1(u1_struct_0(sK0),sK1,X5)))) )),
% 0.21/0.66    inference(superposition,[],[f74,f454])).
% 0.21/0.66  fof(f454,plain,(
% 0.21/0.66    ( ! [X1] : (k7_subset_1(u1_struct_0(sK0),sK1,X1) = k3_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,X1),sK1)) )),
% 0.21/0.66    inference(superposition,[],[f102,f213])).
% 0.21/0.66  fof(f213,plain,(
% 0.21/0.66    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0))) )),
% 0.21/0.66    inference(resolution,[],[f76,f48])).
% 0.21/0.66  fof(f76,plain,(
% 0.21/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2))) )),
% 0.21/0.66    inference(definition_unfolding,[],[f70,f58])).
% 0.21/0.66  fof(f70,plain,(
% 0.21/0.66    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.66    inference(cnf_transformation,[],[f34])).
% 0.21/0.66  fof(f34,plain,(
% 0.21/0.66    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.66    inference(ennf_transformation,[],[f12])).
% 0.21/0.66  fof(f12,axiom,(
% 0.21/0.66    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.21/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.21/0.66  fof(f102,plain,(
% 0.21/0.66    ( ! [X2,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)) )),
% 0.21/0.66    inference(resolution,[],[f60,f73])).
% 0.21/0.66  fof(f1316,plain,(
% 0.21/0.66    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_2),
% 0.21/0.66    inference(forward_demodulation,[],[f1306,f286])).
% 0.21/0.66  fof(f286,plain,(
% 0.21/0.66    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 0.21/0.66    inference(subsumption_resolution,[],[f282,f47])).
% 0.21/0.66  fof(f282,plain,(
% 0.21/0.66    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.21/0.66    inference(resolution,[],[f52,f48])).
% 0.21/0.66  fof(f52,plain,(
% 0.21/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 0.21/0.66    inference(cnf_transformation,[],[f23])).
% 0.21/0.66  fof(f23,plain,(
% 0.21/0.66    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.66    inference(ennf_transformation,[],[f18])).
% 0.21/0.66  fof(f18,axiom,(
% 0.21/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.21/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 0.21/0.66  fof(f1306,plain,(
% 0.21/0.66    k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_2),
% 0.21/0.66    inference(resolution,[],[f1297,f601])).
% 0.21/0.66  fof(f601,plain,(
% 0.21/0.66    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | k2_xboole_0(sK1,X0) = k4_subset_1(u1_struct_0(sK0),sK1,X0)) )),
% 0.21/0.66    inference(resolution,[],[f245,f48])).
% 0.21/0.66  fof(f245,plain,(
% 0.21/0.66    ( ! [X2,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X3)) | k2_xboole_0(X1,X2) = k4_subset_1(X3,X1,X2) | ~r1_tarski(X2,X3)) )),
% 0.21/0.66    inference(resolution,[],[f72,f69])).
% 0.21/0.66  fof(f72,plain,(
% 0.21/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.66    inference(cnf_transformation,[],[f37])).
% 0.21/0.66  fof(f37,plain,(
% 0.21/0.66    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.66    inference(flattening,[],[f36])).
% 0.21/0.66  fof(f36,plain,(
% 0.21/0.66    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.21/0.66    inference(ennf_transformation,[],[f11])).
% 0.21/0.66  fof(f11,axiom,(
% 0.21/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 0.21/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.21/0.66  fof(f1297,plain,(
% 0.21/0.66    r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) | ~spl2_2),
% 0.21/0.66    inference(superposition,[],[f1277,f572])).
% 0.21/0.66  fof(f572,plain,(
% 0.21/0.66    u1_struct_0(sK0) = k2_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.21/0.66    inference(backward_demodulation,[],[f339,f490])).
% 0.21/0.66  fof(f490,plain,(
% 0.21/0.66    u1_struct_0(sK0) = k2_xboole_0(sK1,u1_struct_0(sK0))),
% 0.21/0.66    inference(forward_demodulation,[],[f478,f51])).
% 0.21/0.66  fof(f478,plain,(
% 0.21/0.66    k2_xboole_0(sK1,u1_struct_0(sK0)) = k2_xboole_0(u1_struct_0(sK0),k1_xboole_0)),
% 0.21/0.66    inference(backward_demodulation,[],[f140,f472])).
% 0.21/0.66  fof(f140,plain,(
% 0.21/0.66    k2_xboole_0(u1_struct_0(sK0),k5_xboole_0(sK1,sK1)) = k2_xboole_0(sK1,u1_struct_0(sK0))),
% 0.21/0.66    inference(forward_demodulation,[],[f134,f57])).
% 0.21/0.66  fof(f134,plain,(
% 0.21/0.66    k2_xboole_0(u1_struct_0(sK0),sK1) = k2_xboole_0(u1_struct_0(sK0),k5_xboole_0(sK1,sK1))),
% 0.21/0.66    inference(superposition,[],[f74,f101])).
% 0.21/0.66  fof(f101,plain,(
% 0.21/0.66    sK1 = k3_xboole_0(sK1,u1_struct_0(sK0))),
% 0.21/0.66    inference(resolution,[],[f60,f98])).
% 0.21/0.66  fof(f98,plain,(
% 0.21/0.66    r1_tarski(sK1,u1_struct_0(sK0))),
% 0.21/0.66    inference(resolution,[],[f68,f48])).
% 0.21/0.66  fof(f68,plain,(
% 0.21/0.66    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.66    inference(cnf_transformation,[],[f45])).
% 0.21/0.66  fof(f339,plain,(
% 0.21/0.66    k2_xboole_0(sK1,u1_struct_0(sK0)) = k2_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.21/0.66    inference(superposition,[],[f74,f167])).
% 0.21/0.66  fof(f167,plain,(
% 0.21/0.66    k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k3_xboole_0(u1_struct_0(sK0),sK1))),
% 0.21/0.66    inference(resolution,[],[f75,f48])).
% 0.21/0.66  fof(f1277,plain,(
% 0.21/0.66    ( ! [X10] : (r1_tarski(k2_tops_1(sK0,sK1),k2_xboole_0(sK1,X10))) ) | ~spl2_2),
% 0.21/0.66    inference(superposition,[],[f1237,f86])).
% 0.21/0.66  fof(f1237,plain,(
% 0.21/0.66    ( ! [X4,X3] : (r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X3),k2_xboole_0(sK1,X4))) )),
% 0.21/0.66    inference(subsumption_resolution,[],[f1236,f160])).
% 0.21/0.66  fof(f1236,plain,(
% 0.21/0.66    ( ! [X4,X3] : (~r1_tarski(k1_xboole_0,X4) | r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X3),k2_xboole_0(sK1,X4))) )),
% 0.21/0.66    inference(forward_demodulation,[],[f1229,f472])).
% 0.21/0.66  fof(f1229,plain,(
% 0.21/0.66    ( ! [X4,X3] : (~r1_tarski(k5_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,X3),k7_subset_1(u1_struct_0(sK0),sK1,X3)),X4) | r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X3),k2_xboole_0(sK1,X4))) )),
% 0.21/0.66    inference(superposition,[],[f77,f454])).
% 0.21/0.66  fof(f55,plain,(
% 0.21/0.66    ( ! [X0,X1] : (k2_pre_topc(X0,X1) != X1 | v4_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.66    inference(cnf_transformation,[],[f26])).
% 0.21/0.66  fof(f89,plain,(
% 0.21/0.66    spl2_1 | spl2_2),
% 0.21/0.66    inference(avatar_split_clause,[],[f49,f85,f81])).
% 0.21/0.66  fof(f49,plain,(
% 0.21/0.66    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 0.21/0.66    inference(cnf_transformation,[],[f42])).
% 0.21/0.66  fof(f88,plain,(
% 0.21/0.66    ~spl2_1 | ~spl2_2),
% 0.21/0.66    inference(avatar_split_clause,[],[f50,f85,f81])).
% 0.21/0.66  fof(f50,plain,(
% 0.21/0.66    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 0.21/0.66    inference(cnf_transformation,[],[f42])).
% 0.21/0.66  % SZS output end Proof for theBenchmark
% 0.21/0.66  % (3534)------------------------------
% 0.21/0.66  % (3534)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.66  % (3534)Termination reason: Refutation
% 0.21/0.66  
% 0.21/0.66  % (3534)Memory used [KB]: 11769
% 0.21/0.66  % (3534)Time elapsed: 0.198 s
% 0.21/0.66  % (3534)------------------------------
% 0.21/0.66  % (3534)------------------------------
% 0.21/0.66  % (3527)Success in time 0.299 s
%------------------------------------------------------------------------------
