%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1122+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:08 EST 2020

% Result     : Theorem 28.57s
% Output     : Refutation 28.57s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 704 expanded)
%              Number of leaves         :   17 ( 228 expanded)
%              Depth                    :   23
%              Number of atoms          :  300 (3041 expanded)
%              Number of equality atoms :   61 ( 731 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24455,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3634,f3802,f4049,f24160,f24444])).

fof(f24444,plain,
    ( ~ spl99_2
    | ~ spl99_3 ),
    inference(avatar_contradiction_clause,[],[f24443])).

fof(f24443,plain,
    ( $false
    | ~ spl99_2
    | ~ spl99_3 ),
    inference(subsumption_resolution,[],[f24442,f3637])).

fof(f3637,plain,
    ( ~ v3_pre_topc(sK23,sK22)
    | ~ spl99_2 ),
    inference(resolution,[],[f3633,f2540])).

fof(f2540,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2274])).

fof(f2274,plain,(
    ! [X0,X1] :
      ( ( ~ v3_pre_topc(X1,X0)
        & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
        & v2_pre_topc(X0) )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f2235])).

fof(f2235,plain,(
    ! [X0,X1] :
      ( ( ~ v3_pre_topc(X1,X0)
        & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
        & v2_pre_topc(X0) )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f3633,plain,
    ( sP0(sK22,sK23)
    | ~ spl99_2 ),
    inference(avatar_component_clause,[],[f3632])).

fof(f3632,plain,
    ( spl99_2
  <=> sP0(sK22,sK23) ),
    introduced(avatar_definition,[new_symbols(naming,[spl99_2])])).

fof(f24442,plain,
    ( v3_pre_topc(sK23,sK22)
    | ~ spl99_2
    | ~ spl99_3 ),
    inference(forward_demodulation,[],[f24441,f24141])).

fof(f24141,plain,(
    sK23 = k7_subset_1(u1_struct_0(sK22),u1_struct_0(sK22),k4_xboole_0(u1_struct_0(sK22),sK23)) ),
    inference(subsumption_resolution,[],[f24119,f3345])).

fof(f3345,plain,(
    m1_subset_1(u1_struct_0(sK22),k1_zfmisc_1(u1_struct_0(sK22))) ),
    inference(backward_demodulation,[],[f3326,f3327])).

fof(f3327,plain,(
    u1_struct_0(sK22) = k2_struct_0(sK22) ),
    inference(resolution,[],[f3292,f2568])).

fof(f2568,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f1873])).

fof(f1873,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1771])).

fof(f1771,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f3292,plain,(
    l1_struct_0(sK22) ),
    inference(resolution,[],[f2541,f2829])).

fof(f2829,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2044])).

fof(f2044,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1780])).

fof(f1780,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f2541,plain,(
    l1_pre_topc(sK22) ),
    inference(cnf_transformation,[],[f2277])).

fof(f2277,plain,
    ( ( sP0(sK22,sK23)
      | ( k7_subset_1(u1_struct_0(sK22),k2_struct_0(sK22),sK23) != k2_pre_topc(sK22,k7_subset_1(u1_struct_0(sK22),k2_struct_0(sK22),sK23))
        & v3_pre_topc(sK23,sK22) ) )
    & m1_subset_1(sK23,k1_zfmisc_1(u1_struct_0(sK22)))
    & l1_pre_topc(sK22) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK22,sK23])],[f2236,f2276,f2275])).

fof(f2275,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( sP0(X0,X1)
              | ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
                & v3_pre_topc(X1,X0) ) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( sP0(sK22,X1)
            | ( k7_subset_1(u1_struct_0(sK22),k2_struct_0(sK22),X1) != k2_pre_topc(sK22,k7_subset_1(u1_struct_0(sK22),k2_struct_0(sK22),X1))
              & v3_pre_topc(X1,sK22) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK22))) )
      & l1_pre_topc(sK22) ) ),
    introduced(choice_axiom,[])).

fof(f2276,plain,
    ( ? [X1] :
        ( ( sP0(sK22,X1)
          | ( k7_subset_1(u1_struct_0(sK22),k2_struct_0(sK22),X1) != k2_pre_topc(sK22,k7_subset_1(u1_struct_0(sK22),k2_struct_0(sK22),X1))
            & v3_pre_topc(X1,sK22) ) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK22))) )
   => ( ( sP0(sK22,sK23)
        | ( k7_subset_1(u1_struct_0(sK22),k2_struct_0(sK22),sK23) != k2_pre_topc(sK22,k7_subset_1(u1_struct_0(sK22),k2_struct_0(sK22),sK23))
          & v3_pre_topc(sK23,sK22) ) )
      & m1_subset_1(sK23,k1_zfmisc_1(u1_struct_0(sK22))) ) ),
    introduced(choice_axiom,[])).

fof(f2236,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( sP0(X0,X1)
            | ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              & v3_pre_topc(X1,X0) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f1847,f2235])).

fof(f1847,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ~ v3_pre_topc(X1,X0)
              & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              & v2_pre_topc(X0) )
            | ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              & v3_pre_topc(X1,X0) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f1846])).

fof(f1846,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ~ v3_pre_topc(X1,X0)
              & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              & v2_pre_topc(X0) )
            | ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              & v3_pre_topc(X1,X0) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1836])).

fof(f1836,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
                  & v2_pre_topc(X0) )
               => v3_pre_topc(X1,X0) )
              & ( v3_pre_topc(X1,X0)
               => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f1835])).

fof(f1835,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
                & v2_pre_topc(X0) )
             => v3_pre_topc(X1,X0) )
            & ( v3_pre_topc(X1,X0)
             => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_pre_topc)).

fof(f3326,plain,(
    m1_subset_1(k2_struct_0(sK22),k1_zfmisc_1(u1_struct_0(sK22))) ),
    inference(resolution,[],[f3292,f2567])).

fof(f2567,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f1872])).

fof(f1872,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1779])).

fof(f1779,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f24119,plain,
    ( sK23 = k7_subset_1(u1_struct_0(sK22),u1_struct_0(sK22),k4_xboole_0(u1_struct_0(sK22),sK23))
    | ~ m1_subset_1(u1_struct_0(sK22),k1_zfmisc_1(u1_struct_0(sK22))) ),
    inference(superposition,[],[f3559,f2552])).

fof(f2552,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1860])).

fof(f1860,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f494])).

fof(f494,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f3559,plain,(
    sK23 = k7_subset_1(u1_struct_0(sK22),u1_struct_0(sK22),k7_subset_1(u1_struct_0(sK22),u1_struct_0(sK22),sK23)) ),
    inference(forward_demodulation,[],[f3558,f3327])).

fof(f3558,plain,(
    sK23 = k7_subset_1(u1_struct_0(sK22),k2_struct_0(sK22),k7_subset_1(u1_struct_0(sK22),k2_struct_0(sK22),sK23)) ),
    inference(subsumption_resolution,[],[f3366,f3292])).

fof(f3366,plain,
    ( sK23 = k7_subset_1(u1_struct_0(sK22),k2_struct_0(sK22),k7_subset_1(u1_struct_0(sK22),k2_struct_0(sK22),sK23))
    | ~ l1_struct_0(sK22) ),
    inference(resolution,[],[f2542,f2566])).

fof(f2566,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f1871])).

fof(f1871,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1815])).

fof(f1815,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_pre_topc)).

fof(f2542,plain,(
    m1_subset_1(sK23,k1_zfmisc_1(u1_struct_0(sK22))) ),
    inference(cnf_transformation,[],[f2277])).

fof(f24441,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK22),u1_struct_0(sK22),k4_xboole_0(u1_struct_0(sK22),sK23)),sK22)
    | ~ spl99_2
    | ~ spl99_3 ),
    inference(forward_demodulation,[],[f24440,f3327])).

fof(f24440,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK22),k2_struct_0(sK22),k4_xboole_0(u1_struct_0(sK22),sK23)),sK22)
    | ~ spl99_2
    | ~ spl99_3 ),
    inference(subsumption_resolution,[],[f24439,f2541])).

fof(f24439,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK22),k2_struct_0(sK22),k4_xboole_0(u1_struct_0(sK22),sK23)),sK22)
    | ~ l1_pre_topc(sK22)
    | ~ spl99_2
    | ~ spl99_3 ),
    inference(subsumption_resolution,[],[f20857,f24426])).

fof(f24426,plain,
    ( v4_pre_topc(k4_xboole_0(u1_struct_0(sK22),sK23),sK22)
    | ~ spl99_2
    | ~ spl99_3 ),
    inference(subsumption_resolution,[],[f24419,f20649])).

fof(f20649,plain,
    ( v2_pre_topc(sK22)
    | ~ spl99_3 ),
    inference(avatar_component_clause,[],[f3795])).

fof(f3795,plain,
    ( spl99_3
  <=> v2_pre_topc(sK22) ),
    introduced(avatar_definition,[new_symbols(naming,[spl99_3])])).

fof(f24419,plain,
    ( v4_pre_topc(k4_xboole_0(u1_struct_0(sK22),sK23),sK22)
    | ~ v2_pre_topc(sK22)
    | ~ spl99_2 ),
    inference(trivial_inequality_removal,[],[f24416])).

fof(f24416,plain,
    ( k4_xboole_0(u1_struct_0(sK22),sK23) != k4_xboole_0(u1_struct_0(sK22),sK23)
    | v4_pre_topc(k4_xboole_0(u1_struct_0(sK22),sK23),sK22)
    | ~ v2_pre_topc(sK22)
    | ~ spl99_2 ),
    inference(backward_demodulation,[],[f10289,f24404])).

fof(f24404,plain,
    ( k4_xboole_0(u1_struct_0(sK22),sK23) = k2_pre_topc(sK22,k4_xboole_0(u1_struct_0(sK22),sK23))
    | ~ spl99_2 ),
    inference(forward_demodulation,[],[f3638,f24143])).

fof(f24143,plain,(
    k7_subset_1(u1_struct_0(sK22),u1_struct_0(sK22),sK23) = k4_xboole_0(u1_struct_0(sK22),sK23) ),
    inference(backward_demodulation,[],[f6111,f24141])).

fof(f6111,plain,(
    k4_xboole_0(u1_struct_0(sK22),sK23) = k7_subset_1(u1_struct_0(sK22),u1_struct_0(sK22),k7_subset_1(u1_struct_0(sK22),u1_struct_0(sK22),k4_xboole_0(u1_struct_0(sK22),sK23))) ),
    inference(forward_demodulation,[],[f6110,f3327])).

fof(f6110,plain,(
    k4_xboole_0(u1_struct_0(sK22),sK23) = k7_subset_1(u1_struct_0(sK22),k2_struct_0(sK22),k7_subset_1(u1_struct_0(sK22),k2_struct_0(sK22),k4_xboole_0(u1_struct_0(sK22),sK23))) ),
    inference(subsumption_resolution,[],[f5920,f3292])).

fof(f5920,plain,
    ( k4_xboole_0(u1_struct_0(sK22),sK23) = k7_subset_1(u1_struct_0(sK22),k2_struct_0(sK22),k7_subset_1(u1_struct_0(sK22),k2_struct_0(sK22),k4_xboole_0(u1_struct_0(sK22),sK23)))
    | ~ l1_struct_0(sK22) ),
    inference(resolution,[],[f3625,f2566])).

fof(f3625,plain,(
    m1_subset_1(k4_xboole_0(u1_struct_0(sK22),sK23),k1_zfmisc_1(u1_struct_0(sK22))) ),
    inference(forward_demodulation,[],[f3521,f3520])).

fof(f3520,plain,(
    k3_subset_1(u1_struct_0(sK22),sK23) = k4_xboole_0(u1_struct_0(sK22),sK23) ),
    inference(resolution,[],[f2542,f2761])).

fof(f2761,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1985])).

fof(f1985,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f462])).

fof(f462,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f3521,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK22),sK23),k1_zfmisc_1(u1_struct_0(sK22))) ),
    inference(resolution,[],[f2542,f2762])).

fof(f2762,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1986])).

fof(f1986,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f466])).

fof(f466,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f3638,plain,
    ( k7_subset_1(u1_struct_0(sK22),u1_struct_0(sK22),sK23) = k2_pre_topc(sK22,k7_subset_1(u1_struct_0(sK22),u1_struct_0(sK22),sK23))
    | ~ spl99_2 ),
    inference(forward_demodulation,[],[f3636,f3327])).

fof(f3636,plain,
    ( k7_subset_1(u1_struct_0(sK22),k2_struct_0(sK22),sK23) = k2_pre_topc(sK22,k7_subset_1(u1_struct_0(sK22),k2_struct_0(sK22),sK23))
    | ~ spl99_2 ),
    inference(resolution,[],[f3633,f2539])).

fof(f2539,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2274])).

fof(f10289,plain,
    ( v4_pre_topc(k4_xboole_0(u1_struct_0(sK22),sK23),sK22)
    | k4_xboole_0(u1_struct_0(sK22),sK23) != k2_pre_topc(sK22,k4_xboole_0(u1_struct_0(sK22),sK23))
    | ~ v2_pre_topc(sK22) ),
    inference(subsumption_resolution,[],[f5938,f2541])).

fof(f5938,plain,
    ( v4_pre_topc(k4_xboole_0(u1_struct_0(sK22),sK23),sK22)
    | k4_xboole_0(u1_struct_0(sK22),sK23) != k2_pre_topc(sK22,k4_xboole_0(u1_struct_0(sK22),sK23))
    | ~ v2_pre_topc(sK22)
    | ~ l1_pre_topc(sK22) ),
    inference(resolution,[],[f3625,f2871])).

fof(f2871,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2067])).

fof(f2067,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2066])).

fof(f2066,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1834])).

fof(f1834,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f20857,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK22),k2_struct_0(sK22),k4_xboole_0(u1_struct_0(sK22),sK23)),sK22)
    | ~ v4_pre_topc(k4_xboole_0(u1_struct_0(sK22),sK23),sK22)
    | ~ l1_pre_topc(sK22) ),
    inference(resolution,[],[f3625,f2581])).

fof(f2581,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2295])).

fof(f2295,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f1876])).

fof(f1876,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1773])).

fof(f1773,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_pre_topc)).

fof(f24160,plain,
    ( ~ spl99_1
    | spl99_12 ),
    inference(avatar_contradiction_clause,[],[f24159])).

fof(f24159,plain,
    ( $false
    | ~ spl99_1
    | spl99_12 ),
    inference(subsumption_resolution,[],[f24144,f3630])).

fof(f3630,plain,
    ( v3_pre_topc(sK23,sK22)
    | ~ spl99_1 ),
    inference(avatar_component_clause,[],[f3629])).

fof(f3629,plain,
    ( spl99_1
  <=> v3_pre_topc(sK23,sK22) ),
    introduced(avatar_definition,[new_symbols(naming,[spl99_1])])).

fof(f24144,plain,
    ( ~ v3_pre_topc(sK23,sK22)
    | spl99_12 ),
    inference(backward_demodulation,[],[f12435,f24141])).

fof(f12435,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK22),u1_struct_0(sK22),k4_xboole_0(u1_struct_0(sK22),sK23)),sK22)
    | spl99_12 ),
    inference(forward_demodulation,[],[f12434,f3327])).

fof(f12434,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK22),k2_struct_0(sK22),k4_xboole_0(u1_struct_0(sK22),sK23)),sK22)
    | spl99_12 ),
    inference(subsumption_resolution,[],[f12433,f2541])).

fof(f12433,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK22),k2_struct_0(sK22),k4_xboole_0(u1_struct_0(sK22),sK23)),sK22)
    | ~ l1_pre_topc(sK22)
    | spl99_12 ),
    inference(subsumption_resolution,[],[f12255,f6127])).

fof(f6127,plain,
    ( ~ v4_pre_topc(k4_xboole_0(u1_struct_0(sK22),sK23),sK22)
    | spl99_12 ),
    inference(subsumption_resolution,[],[f6126,f2541])).

fof(f6126,plain,
    ( ~ v4_pre_topc(k4_xboole_0(u1_struct_0(sK22),sK23),sK22)
    | ~ l1_pre_topc(sK22)
    | spl99_12 ),
    inference(subsumption_resolution,[],[f5937,f4069])).

fof(f4069,plain,
    ( k4_xboole_0(u1_struct_0(sK22),sK23) != k2_pre_topc(sK22,k4_xboole_0(u1_struct_0(sK22),sK23))
    | spl99_12 ),
    inference(subsumption_resolution,[],[f4054,f3345])).

fof(f4054,plain,
    ( k4_xboole_0(u1_struct_0(sK22),sK23) != k2_pre_topc(sK22,k4_xboole_0(u1_struct_0(sK22),sK23))
    | ~ m1_subset_1(u1_struct_0(sK22),k1_zfmisc_1(u1_struct_0(sK22)))
    | spl99_12 ),
    inference(superposition,[],[f4048,f2552])).

fof(f4048,plain,
    ( k7_subset_1(u1_struct_0(sK22),u1_struct_0(sK22),sK23) != k2_pre_topc(sK22,k7_subset_1(u1_struct_0(sK22),u1_struct_0(sK22),sK23))
    | spl99_12 ),
    inference(avatar_component_clause,[],[f4047])).

fof(f4047,plain,
    ( spl99_12
  <=> k7_subset_1(u1_struct_0(sK22),u1_struct_0(sK22),sK23) = k2_pre_topc(sK22,k7_subset_1(u1_struct_0(sK22),u1_struct_0(sK22),sK23)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl99_12])])).

fof(f5937,plain,
    ( k4_xboole_0(u1_struct_0(sK22),sK23) = k2_pre_topc(sK22,k4_xboole_0(u1_struct_0(sK22),sK23))
    | ~ v4_pre_topc(k4_xboole_0(u1_struct_0(sK22),sK23),sK22)
    | ~ l1_pre_topc(sK22) ),
    inference(resolution,[],[f3625,f2870])).

fof(f2870,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2067])).

fof(f12255,plain,
    ( v4_pre_topc(k4_xboole_0(u1_struct_0(sK22),sK23),sK22)
    | ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK22),k2_struct_0(sK22),k4_xboole_0(u1_struct_0(sK22),sK23)),sK22)
    | ~ l1_pre_topc(sK22) ),
    inference(resolution,[],[f3625,f2582])).

fof(f2582,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2295])).

fof(f4049,plain,
    ( spl99_2
    | ~ spl99_12 ),
    inference(avatar_split_clause,[],[f3330,f4047,f3632])).

fof(f3330,plain,
    ( k7_subset_1(u1_struct_0(sK22),u1_struct_0(sK22),sK23) != k2_pre_topc(sK22,k7_subset_1(u1_struct_0(sK22),u1_struct_0(sK22),sK23))
    | sP0(sK22,sK23) ),
    inference(backward_demodulation,[],[f2544,f3327])).

fof(f2544,plain,
    ( sP0(sK22,sK23)
    | k7_subset_1(u1_struct_0(sK22),k2_struct_0(sK22),sK23) != k2_pre_topc(sK22,k7_subset_1(u1_struct_0(sK22),k2_struct_0(sK22),sK23)) ),
    inference(cnf_transformation,[],[f2277])).

fof(f3802,plain,
    ( ~ spl99_2
    | spl99_3 ),
    inference(avatar_contradiction_clause,[],[f3801])).

fof(f3801,plain,
    ( $false
    | ~ spl99_2
    | spl99_3 ),
    inference(subsumption_resolution,[],[f3796,f3635])).

fof(f3635,plain,
    ( v2_pre_topc(sK22)
    | ~ spl99_2 ),
    inference(resolution,[],[f3633,f2538])).

fof(f2538,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2274])).

fof(f3796,plain,
    ( ~ v2_pre_topc(sK22)
    | spl99_3 ),
    inference(avatar_component_clause,[],[f3795])).

fof(f3634,plain,
    ( spl99_1
    | spl99_2 ),
    inference(avatar_split_clause,[],[f2543,f3632,f3629])).

fof(f2543,plain,
    ( sP0(sK22,sK23)
    | v3_pre_topc(sK23,sK22) ),
    inference(cnf_transformation,[],[f2277])).
%------------------------------------------------------------------------------
