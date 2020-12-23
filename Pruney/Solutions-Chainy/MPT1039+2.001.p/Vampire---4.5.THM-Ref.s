%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  195 ( 453 expanded)
%              Number of leaves         :   27 ( 177 expanded)
%              Depth                    :   12
%              Number of atoms          :  936 (2022 expanded)
%              Number of equality atoms :   46 ( 197 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f668,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f43,f48,f73,f78,f83,f93,f117,f167,f173,f181,f294,f350,f355,f405,f419,f442,f449,f495,f514,f521,f529,f583,f655,f666,f667])).

fof(f667,plain,
    ( k1_xboole_0 != sK0
    | v1_funct_1(sK4(sK0,sK1,sK2,sK3))
    | ~ v1_funct_1(sK4(k1_xboole_0,sK1,sK2,sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f666,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_11
    | ~ spl5_33
    | spl5_35 ),
    inference(avatar_contradiction_clause,[],[f665])).

fof(f665,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_11
    | ~ spl5_33
    | spl5_35 ),
    inference(subsumption_resolution,[],[f645,f654])).

fof(f654,plain,
    ( ~ r1_partfun1(sK3,sK4(k1_xboole_0,k1_xboole_0,sK2,sK3))
    | spl5_35 ),
    inference(avatar_component_clause,[],[f652])).

fof(f652,plain,
    ( spl5_35
  <=> r1_partfun1(sK3,sK4(k1_xboole_0,k1_xboole_0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f645,plain,
    ( r1_partfun1(sK3,sK4(k1_xboole_0,k1_xboole_0,sK2,sK3))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_11
    | ~ spl5_33 ),
    inference(subsumption_resolution,[],[f644,f47])).

fof(f47,plain,
    ( r1_partfun1(sK2,sK3)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl5_3
  <=> r1_partfun1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f644,plain,
    ( ~ r1_partfun1(sK2,sK3)
    | r1_partfun1(sK3,sK4(k1_xboole_0,k1_xboole_0,sK2,sK3))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_11
    | ~ spl5_33 ),
    inference(subsumption_resolution,[],[f641,f37])).

fof(f37,plain,
    ( v1_funct_1(sK3)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl5_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f641,plain,
    ( ~ v1_funct_1(sK3)
    | ~ r1_partfun1(sK2,sK3)
    | r1_partfun1(sK3,sK4(k1_xboole_0,k1_xboole_0,sK2,sK3))
    | ~ spl5_2
    | ~ spl5_11
    | ~ spl5_33 ),
    inference(resolution,[],[f585,f166])).

fof(f166,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl5_11
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f585,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(X1)
        | ~ r1_partfun1(sK2,X1)
        | r1_partfun1(X1,sK4(k1_xboole_0,k1_xboole_0,sK2,X1)) )
    | ~ spl5_2
    | ~ spl5_33 ),
    inference(resolution,[],[f582,f62])).

fof(f62,plain,
    ( ! [X14,X15] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X14)))
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X14)))
        | ~ r1_partfun1(sK2,X15)
        | r1_partfun1(X15,sK4(k1_xboole_0,X14,sK2,X15)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f42,f29])).

fof(f29,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ r1_partfun1(X2,X3)
      | r1_partfun1(X3,sK4(k1_xboole_0,X1,X2,X3)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | ~ r1_partfun1(X2,X3)
      | r1_partfun1(X3,sK4(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ? [X4] :
              ( r1_partfun1(X3,X4)
              & r1_partfun1(X2,X4)
              & v1_partfun1(X4,X0)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X4) )
          | ~ r1_partfun1(X2,X3)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ? [X4] :
              ( r1_partfun1(X3,X4)
              & r1_partfun1(X2,X4)
              & v1_partfun1(X4,X0)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X4) )
          | ~ r1_partfun1(X2,X3)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ~ ( ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_1(X4) )
                 => ~ ( r1_partfun1(X3,X4)
                      & r1_partfun1(X2,X4)
                      & v1_partfun1(X4,X0) ) )
              & r1_partfun1(X2,X3)
              & ( k1_xboole_0 = X1
               => k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_partfun1)).

fof(f42,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl5_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f582,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f580])).

fof(f580,plain,
    ( spl5_33
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f655,plain,
    ( ~ spl5_35
    | ~ spl5_4
    | ~ spl5_5
    | spl5_9 ),
    inference(avatar_split_clause,[],[f591,f114,f70,f66,f652])).

fof(f66,plain,
    ( spl5_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f70,plain,
    ( spl5_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f114,plain,
    ( spl5_9
  <=> r1_partfun1(sK3,sK4(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f591,plain,
    ( ~ r1_partfun1(sK3,sK4(k1_xboole_0,k1_xboole_0,sK2,sK3))
    | ~ spl5_4
    | ~ spl5_5
    | spl5_9 ),
    inference(forward_demodulation,[],[f590,f68])).

fof(f68,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f590,plain,
    ( ~ r1_partfun1(sK3,sK4(sK0,k1_xboole_0,sK2,sK3))
    | ~ spl5_5
    | spl5_9 ),
    inference(forward_demodulation,[],[f115,f71])).

fof(f71,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f70])).

fof(f115,plain,
    ( ~ r1_partfun1(sK3,sK4(sK0,sK1,sK2,sK3))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f114])).

fof(f583,plain,
    ( spl5_33
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f564,f80,f70,f66,f580])).

fof(f80,plain,
    ( spl5_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f564,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f543,f68])).

fof(f543,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(superposition,[],[f82,f71])).

fof(f82,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f80])).

fof(f529,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | spl5_32 ),
    inference(avatar_contradiction_clause,[],[f528])).

fof(f528,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | spl5_32 ),
    inference(subsumption_resolution,[],[f527,f82])).

fof(f527,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | ~ spl5_6
    | spl5_32 ),
    inference(subsumption_resolution,[],[f526,f47])).

fof(f526,plain,
    ( ~ r1_partfun1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_1
    | ~ spl5_2
    | spl5_5
    | ~ spl5_6
    | spl5_32 ),
    inference(subsumption_resolution,[],[f525,f72])).

fof(f72,plain,
    ( k1_xboole_0 != sK1
    | spl5_5 ),
    inference(avatar_component_clause,[],[f70])).

fof(f525,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_partfun1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6
    | spl5_32 ),
    inference(subsumption_resolution,[],[f524,f77])).

fof(f77,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl5_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f524,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1
    | ~ r1_partfun1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_1
    | ~ spl5_2
    | spl5_32 ),
    inference(subsumption_resolution,[],[f523,f37])).

fof(f523,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1
    | ~ r1_partfun1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_2
    | spl5_32 ),
    inference(resolution,[],[f520,f59])).

fof(f59,plain,
    ( ! [X6,X7,X5] :
        ( v1_partfun1(sK4(X5,X6,sK2,X7),X5)
        | ~ v1_funct_1(X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | k1_xboole_0 = X6
        | ~ r1_partfun1(sK2,X7)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) )
    | ~ spl5_2 ),
    inference(resolution,[],[f42,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r1_partfun1(X2,X3)
      | v1_partfun1(sK4(X0,X1,X2,X3),X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f520,plain,
    ( ~ v1_partfun1(sK4(sK0,sK1,sK2,sK3),sK0)
    | spl5_32 ),
    inference(avatar_component_clause,[],[f518])).

fof(f518,plain,
    ( spl5_32
  <=> v1_partfun1(sK4(sK0,sK1,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f521,plain,
    ( ~ spl5_32
    | ~ spl5_8
    | ~ spl5_30
    | spl5_31 ),
    inference(avatar_split_clause,[],[f516,f511,f484,f90,f518])).

fof(f90,plain,
    ( spl5_8
  <=> v1_funct_1(sK4(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f484,plain,
    ( spl5_30
  <=> m1_subset_1(sK4(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f511,plain,
    ( spl5_31
  <=> v1_funct_2(sK4(sK0,sK1,sK2,sK3),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f516,plain,
    ( ~ v1_partfun1(sK4(sK0,sK1,sK2,sK3),sK0)
    | ~ spl5_8
    | ~ spl5_30
    | spl5_31 ),
    inference(subsumption_resolution,[],[f515,f485])).

fof(f485,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f484])).

fof(f515,plain,
    ( ~ v1_partfun1(sK4(sK0,sK1,sK2,sK3),sK0)
    | ~ m1_subset_1(sK4(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_8
    | spl5_31 ),
    inference(resolution,[],[f513,f94])).

fof(f94,plain,
    ( ! [X0,X1] :
        ( v1_funct_2(sK4(sK0,sK1,sK2,sK3),X0,X1)
        | ~ v1_partfun1(sK4(sK0,sK1,sK2,sK3),X0)
        | ~ m1_subset_1(sK4(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl5_8 ),
    inference(resolution,[],[f92,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f92,plain,
    ( v1_funct_1(sK4(sK0,sK1,sK2,sK3))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f90])).

fof(f513,plain,
    ( ~ v1_funct_2(sK4(sK0,sK1,sK2,sK3),sK0,sK1)
    | spl5_31 ),
    inference(avatar_component_clause,[],[f511])).

fof(f514,plain,
    ( ~ spl5_31
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_26
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f509,f484,f446,f114,f90,f511])).

fof(f446,plain,
    ( spl5_26
  <=> r1_partfun1(sK2,sK4(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f509,plain,
    ( ~ v1_funct_2(sK4(sK0,sK1,sK2,sK3),sK0,sK1)
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_26
    | ~ spl5_30 ),
    inference(subsumption_resolution,[],[f508,f448])).

fof(f448,plain,
    ( r1_partfun1(sK2,sK4(sK0,sK1,sK2,sK3))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f446])).

fof(f508,plain,
    ( ~ v1_funct_2(sK4(sK0,sK1,sK2,sK3),sK0,sK1)
    | ~ r1_partfun1(sK2,sK4(sK0,sK1,sK2,sK3))
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_30 ),
    inference(subsumption_resolution,[],[f127,f485])).

fof(f127,plain,
    ( ~ v1_funct_2(sK4(sK0,sK1,sK2,sK3),sK0,sK1)
    | ~ m1_subset_1(sK4(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ r1_partfun1(sK2,sK4(sK0,sK1,sK2,sK3))
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f122,f92])).

fof(f122,plain,
    ( ~ v1_funct_2(sK4(sK0,sK1,sK2,sK3),sK0,sK1)
    | ~ m1_subset_1(sK4(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ r1_partfun1(sK2,sK4(sK0,sK1,sK2,sK3))
    | ~ v1_funct_1(sK4(sK0,sK1,sK2,sK3))
    | ~ spl5_9 ),
    inference(resolution,[],[f116,f11])).

fof(f11,plain,(
    ! [X4] :
      ( ~ r1_partfun1(sK3,X4)
      | ~ v1_funct_2(X4,sK0,sK1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r1_partfun1(sK2,X4)
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r1_partfun1(X3,X4)
              | ~ r1_partfun1(X2,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X4,X0,X1)
              | ~ v1_funct_1(X4) )
          & r1_partfun1(X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r1_partfun1(X3,X4)
              | ~ r1_partfun1(X2,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X4,X0,X1)
              | ~ v1_funct_1(X4) )
          & r1_partfun1(X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X3) )
           => ~ ( ! [X4] :
                    ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      & v1_funct_2(X4,X0,X1)
                      & v1_funct_1(X4) )
                   => ~ ( r1_partfun1(X3,X4)
                        & r1_partfun1(X2,X4) ) )
                & r1_partfun1(X2,X3)
                & ( k1_xboole_0 = X1
                 => k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

% (11526)Termination reason: Refutation not found, incomplete strategy

% (11526)Memory used [KB]: 10618
% (11526)Time elapsed: 0.080 s
% (11526)------------------------------
% (11526)------------------------------
fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ~ ( ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_2(X4,X0,X1)
                    & v1_funct_1(X4) )
                 => ~ ( r1_partfun1(X3,X4)
                      & r1_partfun1(X2,X4) ) )
              & r1_partfun1(X2,X3)
              & ( k1_xboole_0 = X1
               => k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_2)).

fof(f116,plain,
    ( r1_partfun1(sK3,sK4(sK0,sK1,sK2,sK3))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f114])).

fof(f495,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | spl5_30 ),
    inference(avatar_contradiction_clause,[],[f494])).

fof(f494,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | spl5_30 ),
    inference(subsumption_resolution,[],[f493,f42])).

fof(f493,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl5_1
    | ~ spl5_3
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | spl5_30 ),
    inference(subsumption_resolution,[],[f492,f47])).

fof(f492,plain,
    ( ~ r1_partfun1(sK2,sK3)
    | ~ v1_funct_1(sK2)
    | ~ spl5_1
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | spl5_30 ),
    inference(subsumption_resolution,[],[f491,f72])).

fof(f491,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_partfun1(sK2,sK3)
    | ~ v1_funct_1(sK2)
    | ~ spl5_1
    | ~ spl5_6
    | ~ spl5_7
    | spl5_30 ),
    inference(subsumption_resolution,[],[f490,f77])).

fof(f490,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1
    | ~ r1_partfun1(sK2,sK3)
    | ~ v1_funct_1(sK2)
    | ~ spl5_1
    | ~ spl5_7
    | spl5_30 ),
    inference(subsumption_resolution,[],[f489,f37])).

fof(f489,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1
    | ~ r1_partfun1(sK2,sK3)
    | ~ v1_funct_1(sK2)
    | ~ spl5_7
    | spl5_30 ),
    inference(subsumption_resolution,[],[f488,f82])).

fof(f488,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1
    | ~ r1_partfun1(sK2,sK3)
    | ~ v1_funct_1(sK2)
    | spl5_30 ),
    inference(resolution,[],[f486,f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r1_partfun1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f486,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl5_30 ),
    inference(avatar_component_clause,[],[f484])).

fof(f449,plain,
    ( spl5_26
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f435,f80,f75,f70,f45,f40,f35,f446])).

fof(f435,plain,
    ( r1_partfun1(sK2,sK4(sK0,sK1,sK2,sK3))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f434,f37])).

fof(f434,plain,
    ( ~ v1_funct_1(sK3)
    | r1_partfun1(sK2,sK4(sK0,sK1,sK2,sK3))
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f431,f77])).

fof(f431,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | r1_partfun1(sK2,sK4(sK0,sK1,sK2,sK3))
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | ~ spl5_7 ),
    inference(resolution,[],[f263,f47])).

fof(f263,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(sK2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X0)
        | r1_partfun1(sK2,sK4(sK0,sK1,sK2,X0)) )
    | ~ spl5_2
    | spl5_5
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f102,f72])).

fof(f102,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | k1_xboole_0 = sK1
        | ~ r1_partfun1(sK2,X0)
        | r1_partfun1(sK2,sK4(sK0,sK1,sK2,X0)) )
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(resolution,[],[f60,f82])).

fof(f60,plain,
    ( ! [X10,X8,X9] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | ~ v1_funct_1(X10)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | k1_xboole_0 = X9
        | ~ r1_partfun1(sK2,X10)
        | r1_partfun1(sK2,sK4(X8,X9,sK2,X10)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f42,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r1_partfun1(X2,X3)
      | r1_partfun1(X2,sK4(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f442,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_12
    | ~ spl5_13
    | spl5_14 ),
    inference(avatar_contradiction_clause,[],[f441])).

fof(f441,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_12
    | ~ spl5_13
    | spl5_14 ),
    inference(subsumption_resolution,[],[f202,f197])).

fof(f197,plain,
    ( ~ v1_funct_1(sK4(k1_xboole_0,sK1,sK2,sK3))
    | spl5_14 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl5_14
  <=> v1_funct_1(sK4(k1_xboole_0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f202,plain,
    ( v1_funct_1(sK4(k1_xboole_0,sK1,sK2,sK3))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f201,f37])).

fof(f201,plain,
    ( ~ v1_funct_1(sK3)
    | v1_funct_1(sK4(k1_xboole_0,sK1,sK2,sK3))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f200,f172])).

fof(f172,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f170])).

% (11508)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f170,plain,
    ( spl5_12
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f200,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(sK3)
    | v1_funct_1(sK4(k1_xboole_0,sK1,sK2,sK3))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_13 ),
    inference(resolution,[],[f184,f47])).

fof(f184,plain,
    ( ! [X2] :
        ( ~ r1_partfun1(sK2,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
        | ~ v1_funct_1(X2)
        | v1_funct_1(sK4(k1_xboole_0,sK1,sK2,X2)) )
    | ~ spl5_2
    | ~ spl5_13 ),
    inference(resolution,[],[f180,f64])).

fof(f64,plain,
    ( ! [X19,X18] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18)))
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18)))
        | ~ r1_partfun1(sK2,X19)
        | v1_funct_1(sK4(k1_xboole_0,X18,sK2,X19)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f42,f33])).

fof(f33,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ r1_partfun1(X2,X3)
      | v1_funct_1(sK4(k1_xboole_0,X1,X2,X3)) ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | ~ r1_partfun1(X2,X3)
      | v1_funct_1(sK4(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f180,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl5_13
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f419,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_12
    | ~ spl5_13
    | spl5_25 ),
    inference(avatar_contradiction_clause,[],[f418])).

fof(f418,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_12
    | ~ spl5_13
    | spl5_25 ),
    inference(subsumption_resolution,[],[f417,f42])).

fof(f417,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_12
    | ~ spl5_13
    | spl5_25 ),
    inference(subsumption_resolution,[],[f416,f47])).

fof(f416,plain,
    ( ~ r1_partfun1(sK2,sK3)
    | ~ v1_funct_1(sK2)
    | ~ spl5_1
    | ~ spl5_12
    | ~ spl5_13
    | spl5_25 ),
    inference(subsumption_resolution,[],[f415,f172])).

fof(f415,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ r1_partfun1(sK2,sK3)
    | ~ v1_funct_1(sK2)
    | ~ spl5_1
    | ~ spl5_13
    | spl5_25 ),
    inference(subsumption_resolution,[],[f414,f37])).

fof(f414,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ r1_partfun1(sK2,sK3)
    | ~ v1_funct_1(sK2)
    | ~ spl5_13
    | spl5_25 ),
    inference(subsumption_resolution,[],[f412,f180])).

fof(f412,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ r1_partfun1(sK2,sK3)
    | ~ v1_funct_1(sK2)
    | spl5_25 ),
    inference(resolution,[],[f404,f31])).

fof(f31,plain,(
    ! [X2,X3,X1] :
      ( v1_partfun1(sK4(k1_xboole_0,X1,X2,X3),k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ r1_partfun1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | ~ r1_partfun1(X2,X3)
      | v1_partfun1(sK4(X0,X1,X2,X3),X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f404,plain,
    ( ~ v1_partfun1(sK4(k1_xboole_0,sK1,sK2,sK3),k1_xboole_0)
    | spl5_25 ),
    inference(avatar_component_clause,[],[f402])).

fof(f402,plain,
    ( spl5_25
  <=> v1_partfun1(sK4(k1_xboole_0,sK1,sK2,sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f405,plain,
    ( ~ spl5_25
    | ~ spl5_14
    | ~ spl5_18
    | spl5_20 ),
    inference(avatar_split_clause,[],[f394,f343,f274,f196,f402])).

fof(f274,plain,
    ( spl5_18
  <=> m1_subset_1(sK4(k1_xboole_0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f343,plain,
    ( spl5_20
  <=> v1_funct_2(sK4(k1_xboole_0,sK1,sK2,sK3),k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f394,plain,
    ( ~ v1_partfun1(sK4(k1_xboole_0,sK1,sK2,sK3),k1_xboole_0)
    | ~ spl5_14
    | ~ spl5_18
    | spl5_20 ),
    inference(subsumption_resolution,[],[f393,f275])).

fof(f275,plain,
    ( m1_subset_1(sK4(k1_xboole_0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f274])).

fof(f393,plain,
    ( ~ v1_partfun1(sK4(k1_xboole_0,sK1,sK2,sK3),k1_xboole_0)
    | ~ m1_subset_1(sK4(k1_xboole_0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl5_14
    | spl5_20 ),
    inference(resolution,[],[f203,f345])).

fof(f345,plain,
    ( ~ v1_funct_2(sK4(k1_xboole_0,sK1,sK2,sK3),k1_xboole_0,sK1)
    | spl5_20 ),
    inference(avatar_component_clause,[],[f343])).

fof(f203,plain,
    ( ! [X0,X1] :
        ( v1_funct_2(sK4(k1_xboole_0,sK1,sK2,sK3),X0,X1)
        | ~ v1_partfun1(sK4(k1_xboole_0,sK1,sK2,sK3),X0)
        | ~ m1_subset_1(sK4(k1_xboole_0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl5_14 ),
    inference(resolution,[],[f198,f18])).

fof(f198,plain,
    ( v1_funct_1(sK4(k1_xboole_0,sK1,sK2,sK3))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f196])).

fof(f355,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_12
    | ~ spl5_13
    | spl5_21 ),
    inference(avatar_contradiction_clause,[],[f354])).

fof(f354,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_12
    | ~ spl5_13
    | spl5_21 ),
    inference(subsumption_resolution,[],[f353,f37])).

fof(f353,plain,
    ( ~ v1_funct_1(sK3)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_12
    | ~ spl5_13
    | spl5_21 ),
    inference(subsumption_resolution,[],[f352,f47])).

fof(f352,plain,
    ( ~ r1_partfun1(sK2,sK3)
    | ~ v1_funct_1(sK3)
    | ~ spl5_2
    | ~ spl5_12
    | ~ spl5_13
    | spl5_21 ),
    inference(subsumption_resolution,[],[f351,f172])).

fof(f351,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ r1_partfun1(sK2,sK3)
    | ~ v1_funct_1(sK3)
    | ~ spl5_2
    | ~ spl5_13
    | spl5_21 ),
    inference(resolution,[],[f349,f182])).

fof(f182,plain,
    ( ! [X0] :
        ( r1_partfun1(sK2,sK4(k1_xboole_0,sK1,sK2,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
        | ~ r1_partfun1(sK2,X0)
        | ~ v1_funct_1(X0) )
    | ~ spl5_2
    | ~ spl5_13 ),
    inference(resolution,[],[f180,f63])).

fof(f63,plain,
    ( ! [X17,X16] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X16)))
        | ~ v1_funct_1(X17)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X16)))
        | ~ r1_partfun1(sK2,X17)
        | r1_partfun1(sK2,sK4(k1_xboole_0,X16,sK2,X17)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f42,f30])).

fof(f30,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ r1_partfun1(X2,X3)
      | r1_partfun1(X2,sK4(k1_xboole_0,X1,X2,X3)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | ~ r1_partfun1(X2,X3)
      | r1_partfun1(X2,sK4(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f349,plain,
    ( ~ r1_partfun1(sK2,sK4(k1_xboole_0,sK1,sK2,sK3))
    | spl5_21 ),
    inference(avatar_component_clause,[],[f347])).

fof(f347,plain,
    ( spl5_21
  <=> r1_partfun1(sK2,sK4(k1_xboole_0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f350,plain,
    ( ~ spl5_20
    | ~ spl5_21
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f341,f274,f114,f90,f66,f347,f343])).

fof(f341,plain,
    ( ~ r1_partfun1(sK2,sK4(k1_xboole_0,sK1,sK2,sK3))
    | ~ v1_funct_2(sK4(k1_xboole_0,sK1,sK2,sK3),k1_xboole_0,sK1)
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f340,f68])).

fof(f340,plain,
    ( ~ v1_funct_2(sK4(k1_xboole_0,sK1,sK2,sK3),k1_xboole_0,sK1)
    | ~ r1_partfun1(sK2,sK4(sK0,sK1,sK2,sK3))
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f339,f275])).

fof(f339,plain,
    ( ~ m1_subset_1(sK4(k1_xboole_0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_2(sK4(k1_xboole_0,sK1,sK2,sK3),k1_xboole_0,sK1)
    | ~ r1_partfun1(sK2,sK4(sK0,sK1,sK2,sK3))
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f338,f68])).

fof(f338,plain,
    ( ~ v1_funct_2(sK4(k1_xboole_0,sK1,sK2,sK3),k1_xboole_0,sK1)
    | ~ m1_subset_1(sK4(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ r1_partfun1(sK2,sK4(sK0,sK1,sK2,sK3))
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f127,f68])).

fof(f294,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_12
    | ~ spl5_13
    | spl5_18 ),
    inference(avatar_contradiction_clause,[],[f293])).

fof(f293,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_12
    | ~ spl5_13
    | spl5_18 ),
    inference(subsumption_resolution,[],[f292,f42])).

fof(f292,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_12
    | ~ spl5_13
    | spl5_18 ),
    inference(subsumption_resolution,[],[f291,f47])).

fof(f291,plain,
    ( ~ r1_partfun1(sK2,sK3)
    | ~ v1_funct_1(sK2)
    | ~ spl5_1
    | ~ spl5_12
    | ~ spl5_13
    | spl5_18 ),
    inference(subsumption_resolution,[],[f290,f172])).

fof(f290,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ r1_partfun1(sK2,sK3)
    | ~ v1_funct_1(sK2)
    | ~ spl5_1
    | ~ spl5_13
    | spl5_18 ),
    inference(subsumption_resolution,[],[f289,f37])).

fof(f289,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ r1_partfun1(sK2,sK3)
    | ~ v1_funct_1(sK2)
    | ~ spl5_13
    | spl5_18 ),
    inference(subsumption_resolution,[],[f287,f180])).

fof(f287,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ r1_partfun1(sK2,sK3)
    | ~ v1_funct_1(sK2)
    | spl5_18 ),
    inference(resolution,[],[f276,f32])).

fof(f32,plain,(
    ! [X2,X3,X1] :
      ( m1_subset_1(sK4(k1_xboole_0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ r1_partfun1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | ~ r1_partfun1(X2,X3)
      | m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f276,plain,
    ( ~ m1_subset_1(sK4(k1_xboole_0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | spl5_18 ),
    inference(avatar_component_clause,[],[f274])).

fof(f181,plain,
    ( spl5_13
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f144,f80,f66,f178])).

fof(f144,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(superposition,[],[f82,f68])).

fof(f173,plain,
    ( spl5_12
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f143,f75,f66,f170])).

fof(f143,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(superposition,[],[f77,f68])).

fof(f167,plain,
    ( spl5_11
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f153,f75,f70,f66,f164])).

fof(f153,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f148,f68])).

fof(f148,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(superposition,[],[f77,f71])).

fof(f117,plain,
    ( spl5_9
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f111,f80,f75,f70,f45,f40,f35,f114])).

fof(f111,plain,
    ( r1_partfun1(sK3,sK4(sK0,sK1,sK2,sK3))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f110,f37])).

fof(f110,plain,
    ( ~ v1_funct_1(sK3)
    | r1_partfun1(sK3,sK4(sK0,sK1,sK2,sK3))
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f108,f77])).

fof(f108,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | r1_partfun1(sK3,sK4(sK0,sK1,sK2,sK3))
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | ~ spl5_7 ),
    inference(resolution,[],[f107,f47])).

fof(f107,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(sK2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X0)
        | r1_partfun1(X0,sK4(sK0,sK1,sK2,X0)) )
    | ~ spl5_2
    | spl5_5
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f106,f72])).

fof(f106,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | k1_xboole_0 = sK1
        | ~ r1_partfun1(sK2,X0)
        | r1_partfun1(X0,sK4(sK0,sK1,sK2,X0)) )
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(resolution,[],[f61,f82])).

fof(f61,plain,
    ( ! [X12,X13,X11] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
        | ~ v1_funct_1(X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
        | k1_xboole_0 = X12
        | ~ r1_partfun1(sK2,X13)
        | r1_partfun1(X13,sK4(X11,X12,sK2,X13)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f42,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r1_partfun1(X2,X3)
      | r1_partfun1(X3,sK4(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f93,plain,
    ( spl5_8
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f88,f80,f75,f70,f45,f40,f35,f90])).

fof(f88,plain,
    ( v1_funct_1(sK4(sK0,sK1,sK2,sK3))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f87,f37])).

fof(f87,plain,
    ( ~ v1_funct_1(sK3)
    | v1_funct_1(sK4(sK0,sK1,sK2,sK3))
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f86,f77])).

fof(f86,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | v1_funct_1(sK4(sK0,sK1,sK2,sK3))
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | ~ spl5_7 ),
    inference(resolution,[],[f85,f47])).

fof(f85,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(sK2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X0)
        | v1_funct_1(sK4(sK0,sK1,sK2,X0)) )
    | ~ spl5_2
    | spl5_5
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f84,f72])).

fof(f84,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | k1_xboole_0 = sK1
        | ~ r1_partfun1(sK2,X0)
        | v1_funct_1(sK4(sK0,sK1,sK2,X0)) )
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(resolution,[],[f58,f82])).

fof(f58,plain,
    ( ! [X4,X2,X3] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | k1_xboole_0 = X3
        | ~ r1_partfun1(sK2,X4)
        | v1_funct_1(sK4(X2,X3,sK2,X4)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f42,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r1_partfun1(X2,X3)
      | v1_funct_1(sK4(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f83,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f17,f80])).

fof(f17,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f6])).

fof(f78,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f14,f75])).

fof(f14,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f6])).

fof(f73,plain,
    ( spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f12,f70,f66])).

fof(f12,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f6])).

fof(f48,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f15,f45])).

fof(f15,plain,(
    r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f6])).

fof(f43,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f16,f40])).

fof(f16,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f38,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f13,f35])).

fof(f13,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:51:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (11509)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (11510)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  % (11526)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (11526)Refutation not found, incomplete strategy% (11526)------------------------------
% 0.21/0.51  % (11526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (11518)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (11518)Refutation not found, incomplete strategy% (11518)------------------------------
% 0.21/0.52  % (11518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (11518)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (11518)Memory used [KB]: 6012
% 0.21/0.52  % (11518)Time elapsed: 0.002 s
% 0.21/0.52  % (11518)------------------------------
% 0.21/0.52  % (11518)------------------------------
% 0.21/0.52  % (11512)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.52  % (11509)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f668,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f38,f43,f48,f73,f78,f83,f93,f117,f167,f173,f181,f294,f350,f355,f405,f419,f442,f449,f495,f514,f521,f529,f583,f655,f666,f667])).
% 0.21/0.52  fof(f667,plain,(
% 0.21/0.52    k1_xboole_0 != sK0 | v1_funct_1(sK4(sK0,sK1,sK2,sK3)) | ~v1_funct_1(sK4(k1_xboole_0,sK1,sK2,sK3))),
% 0.21/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.52  fof(f666,plain,(
% 0.21/0.52    ~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_11 | ~spl5_33 | spl5_35),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f665])).
% 0.21/0.52  fof(f665,plain,(
% 0.21/0.52    $false | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_11 | ~spl5_33 | spl5_35)),
% 0.21/0.52    inference(subsumption_resolution,[],[f645,f654])).
% 0.21/0.52  fof(f654,plain,(
% 0.21/0.52    ~r1_partfun1(sK3,sK4(k1_xboole_0,k1_xboole_0,sK2,sK3)) | spl5_35),
% 0.21/0.52    inference(avatar_component_clause,[],[f652])).
% 0.21/0.52  fof(f652,plain,(
% 0.21/0.52    spl5_35 <=> r1_partfun1(sK3,sK4(k1_xboole_0,k1_xboole_0,sK2,sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 0.21/0.52  fof(f645,plain,(
% 0.21/0.52    r1_partfun1(sK3,sK4(k1_xboole_0,k1_xboole_0,sK2,sK3)) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_11 | ~spl5_33)),
% 0.21/0.52    inference(subsumption_resolution,[],[f644,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    r1_partfun1(sK2,sK3) | ~spl5_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    spl5_3 <=> r1_partfun1(sK2,sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.52  fof(f644,plain,(
% 0.21/0.52    ~r1_partfun1(sK2,sK3) | r1_partfun1(sK3,sK4(k1_xboole_0,k1_xboole_0,sK2,sK3)) | (~spl5_1 | ~spl5_2 | ~spl5_11 | ~spl5_33)),
% 0.21/0.52    inference(subsumption_resolution,[],[f641,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    v1_funct_1(sK3) | ~spl5_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    spl5_1 <=> v1_funct_1(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.52  fof(f641,plain,(
% 0.21/0.52    ~v1_funct_1(sK3) | ~r1_partfun1(sK2,sK3) | r1_partfun1(sK3,sK4(k1_xboole_0,k1_xboole_0,sK2,sK3)) | (~spl5_2 | ~spl5_11 | ~spl5_33)),
% 0.21/0.52    inference(resolution,[],[f585,f166])).
% 0.21/0.52  fof(f166,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl5_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f164])).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    spl5_11 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.52  fof(f585,plain,(
% 0.21/0.52    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_1(X1) | ~r1_partfun1(sK2,X1) | r1_partfun1(X1,sK4(k1_xboole_0,k1_xboole_0,sK2,X1))) ) | (~spl5_2 | ~spl5_33)),
% 0.21/0.52    inference(resolution,[],[f582,f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X14,X15] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X14))) | ~v1_funct_1(X15) | ~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X14))) | ~r1_partfun1(sK2,X15) | r1_partfun1(X15,sK4(k1_xboole_0,X14,sK2,X15))) ) | ~spl5_2),
% 0.21/0.52    inference(resolution,[],[f42,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X2,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~r1_partfun1(X2,X3) | r1_partfun1(X3,sK4(k1_xboole_0,X1,X2,X3))) )),
% 0.21/0.52    inference(equality_resolution,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | ~r1_partfun1(X2,X3) | r1_partfun1(X3,sK4(X0,X1,X2,X3))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (! [X3] : (? [X4] : (r1_partfun1(X3,X4) & r1_partfun1(X2,X4) & v1_partfun1(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) | ~r1_partfun1(X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.52    inference(flattening,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (! [X3] : ((? [X4] : ((r1_partfun1(X3,X4) & r1_partfun1(X2,X4) & v1_partfun1(X4,X0)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4))) | ~r1_partfun1(X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => ~(r1_partfun1(X3,X4) & r1_partfun1(X2,X4) & v1_partfun1(X4,X0))) & r1_partfun1(X2,X3) & (k1_xboole_0 = X1 => k1_xboole_0 = X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_partfun1)).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    v1_funct_1(sK2) | ~spl5_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    spl5_2 <=> v1_funct_1(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.52  fof(f582,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl5_33),
% 0.21/0.52    inference(avatar_component_clause,[],[f580])).
% 0.21/0.52  fof(f580,plain,(
% 0.21/0.52    spl5_33 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 0.21/0.52  fof(f655,plain,(
% 0.21/0.52    ~spl5_35 | ~spl5_4 | ~spl5_5 | spl5_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f591,f114,f70,f66,f652])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    spl5_4 <=> k1_xboole_0 = sK0),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    spl5_5 <=> k1_xboole_0 = sK1),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    spl5_9 <=> r1_partfun1(sK3,sK4(sK0,sK1,sK2,sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.52  fof(f591,plain,(
% 0.21/0.52    ~r1_partfun1(sK3,sK4(k1_xboole_0,k1_xboole_0,sK2,sK3)) | (~spl5_4 | ~spl5_5 | spl5_9)),
% 0.21/0.52    inference(forward_demodulation,[],[f590,f68])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | ~spl5_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f66])).
% 0.21/0.52  fof(f590,plain,(
% 0.21/0.52    ~r1_partfun1(sK3,sK4(sK0,k1_xboole_0,sK2,sK3)) | (~spl5_5 | spl5_9)),
% 0.21/0.52    inference(forward_demodulation,[],[f115,f71])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | ~spl5_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f70])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    ~r1_partfun1(sK3,sK4(sK0,sK1,sK2,sK3)) | spl5_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f114])).
% 0.21/0.52  fof(f583,plain,(
% 0.21/0.52    spl5_33 | ~spl5_4 | ~spl5_5 | ~spl5_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f564,f80,f70,f66,f580])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    spl5_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.52  fof(f564,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl5_4 | ~spl5_5 | ~spl5_7)),
% 0.21/0.52    inference(forward_demodulation,[],[f543,f68])).
% 0.21/0.52  fof(f543,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl5_5 | ~spl5_7)),
% 0.21/0.52    inference(superposition,[],[f82,f71])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f80])).
% 0.21/0.52  fof(f529,plain,(
% 0.21/0.52    ~spl5_1 | ~spl5_2 | ~spl5_3 | spl5_5 | ~spl5_6 | ~spl5_7 | spl5_32),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f528])).
% 0.21/0.52  fof(f528,plain,(
% 0.21/0.52    $false | (~spl5_1 | ~spl5_2 | ~spl5_3 | spl5_5 | ~spl5_6 | ~spl5_7 | spl5_32)),
% 0.21/0.52    inference(subsumption_resolution,[],[f527,f82])).
% 0.21/0.52  fof(f527,plain,(
% 0.21/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl5_1 | ~spl5_2 | ~spl5_3 | spl5_5 | ~spl5_6 | spl5_32)),
% 0.21/0.52    inference(subsumption_resolution,[],[f526,f47])).
% 0.21/0.52  fof(f526,plain,(
% 0.21/0.52    ~r1_partfun1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl5_1 | ~spl5_2 | spl5_5 | ~spl5_6 | spl5_32)),
% 0.21/0.52    inference(subsumption_resolution,[],[f525,f72])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    k1_xboole_0 != sK1 | spl5_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f70])).
% 0.21/0.52  fof(f525,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | ~r1_partfun1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl5_1 | ~spl5_2 | ~spl5_6 | spl5_32)),
% 0.21/0.52    inference(subsumption_resolution,[],[f524,f77])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f75])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    spl5_6 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.52  fof(f524,plain,(
% 0.21/0.52    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k1_xboole_0 = sK1 | ~r1_partfun1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl5_1 | ~spl5_2 | spl5_32)),
% 0.21/0.52    inference(subsumption_resolution,[],[f523,f37])).
% 0.21/0.52  fof(f523,plain,(
% 0.21/0.52    ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k1_xboole_0 = sK1 | ~r1_partfun1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl5_2 | spl5_32)),
% 0.21/0.52    inference(resolution,[],[f520,f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X6,X7,X5] : (v1_partfun1(sK4(X5,X6,sK2,X7),X5) | ~v1_funct_1(X7) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | k1_xboole_0 = X6 | ~r1_partfun1(sK2,X7) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))) ) | ~spl5_2),
% 0.21/0.52    inference(resolution,[],[f42,f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r1_partfun1(X2,X3) | v1_partfun1(sK4(X0,X1,X2,X3),X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f520,plain,(
% 0.21/0.52    ~v1_partfun1(sK4(sK0,sK1,sK2,sK3),sK0) | spl5_32),
% 0.21/0.52    inference(avatar_component_clause,[],[f518])).
% 0.21/0.52  fof(f518,plain,(
% 0.21/0.52    spl5_32 <=> v1_partfun1(sK4(sK0,sK1,sK2,sK3),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 0.21/0.52  fof(f521,plain,(
% 0.21/0.52    ~spl5_32 | ~spl5_8 | ~spl5_30 | spl5_31),
% 0.21/0.52    inference(avatar_split_clause,[],[f516,f511,f484,f90,f518])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    spl5_8 <=> v1_funct_1(sK4(sK0,sK1,sK2,sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.52  fof(f484,plain,(
% 0.21/0.52    spl5_30 <=> m1_subset_1(sK4(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.21/0.52  fof(f511,plain,(
% 0.21/0.52    spl5_31 <=> v1_funct_2(sK4(sK0,sK1,sK2,sK3),sK0,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 0.21/0.52  fof(f516,plain,(
% 0.21/0.52    ~v1_partfun1(sK4(sK0,sK1,sK2,sK3),sK0) | (~spl5_8 | ~spl5_30 | spl5_31)),
% 0.21/0.52    inference(subsumption_resolution,[],[f515,f485])).
% 0.21/0.52  fof(f485,plain,(
% 0.21/0.52    m1_subset_1(sK4(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_30),
% 0.21/0.52    inference(avatar_component_clause,[],[f484])).
% 0.21/0.52  fof(f515,plain,(
% 0.21/0.52    ~v1_partfun1(sK4(sK0,sK1,sK2,sK3),sK0) | ~m1_subset_1(sK4(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl5_8 | spl5_31)),
% 0.21/0.52    inference(resolution,[],[f513,f94])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_funct_2(sK4(sK0,sK1,sK2,sK3),X0,X1) | ~v1_partfun1(sK4(sK0,sK1,sK2,sK3),X0) | ~m1_subset_1(sK4(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl5_8),
% 0.21/0.52    inference(resolution,[],[f92,f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X2,X0) | v1_funct_2(X2,X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(flattening,[],[f7])).
% 0.21/0.52  fof(f7,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    v1_funct_1(sK4(sK0,sK1,sK2,sK3)) | ~spl5_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f90])).
% 0.21/0.52  fof(f513,plain,(
% 0.21/0.52    ~v1_funct_2(sK4(sK0,sK1,sK2,sK3),sK0,sK1) | spl5_31),
% 0.21/0.52    inference(avatar_component_clause,[],[f511])).
% 0.21/0.52  fof(f514,plain,(
% 0.21/0.52    ~spl5_31 | ~spl5_8 | ~spl5_9 | ~spl5_26 | ~spl5_30),
% 0.21/0.52    inference(avatar_split_clause,[],[f509,f484,f446,f114,f90,f511])).
% 0.21/0.52  fof(f446,plain,(
% 0.21/0.52    spl5_26 <=> r1_partfun1(sK2,sK4(sK0,sK1,sK2,sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.21/0.52  fof(f509,plain,(
% 0.21/0.52    ~v1_funct_2(sK4(sK0,sK1,sK2,sK3),sK0,sK1) | (~spl5_8 | ~spl5_9 | ~spl5_26 | ~spl5_30)),
% 0.21/0.52    inference(subsumption_resolution,[],[f508,f448])).
% 0.21/0.52  fof(f448,plain,(
% 0.21/0.52    r1_partfun1(sK2,sK4(sK0,sK1,sK2,sK3)) | ~spl5_26),
% 0.21/0.52    inference(avatar_component_clause,[],[f446])).
% 0.21/0.52  fof(f508,plain,(
% 0.21/0.52    ~v1_funct_2(sK4(sK0,sK1,sK2,sK3),sK0,sK1) | ~r1_partfun1(sK2,sK4(sK0,sK1,sK2,sK3)) | (~spl5_8 | ~spl5_9 | ~spl5_30)),
% 0.21/0.52    inference(subsumption_resolution,[],[f127,f485])).
% 0.21/0.52  fof(f127,plain,(
% 0.21/0.52    ~v1_funct_2(sK4(sK0,sK1,sK2,sK3),sK0,sK1) | ~m1_subset_1(sK4(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r1_partfun1(sK2,sK4(sK0,sK1,sK2,sK3)) | (~spl5_8 | ~spl5_9)),
% 0.21/0.52    inference(subsumption_resolution,[],[f122,f92])).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    ~v1_funct_2(sK4(sK0,sK1,sK2,sK3),sK0,sK1) | ~m1_subset_1(sK4(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r1_partfun1(sK2,sK4(sK0,sK1,sK2,sK3)) | ~v1_funct_1(sK4(sK0,sK1,sK2,sK3)) | ~spl5_9),
% 0.21/0.52    inference(resolution,[],[f116,f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ( ! [X4] : (~r1_partfun1(sK3,X4) | ~v1_funct_2(X4,sK0,sK1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r1_partfun1(sK2,X4) | ~v1_funct_1(X4)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (? [X3] : (! [X4] : (~r1_partfun1(X3,X4) | ~r1_partfun1(X2,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4)) & r1_partfun1(X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.21/0.52    inference(flattening,[],[f5])).
% 0.21/0.52  fof(f5,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (? [X3] : ((! [X4] : ((~r1_partfun1(X3,X4) | ~r1_partfun1(X2,X4)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4))) & r1_partfun1(X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4)) => ~(r1_partfun1(X3,X4) & r1_partfun1(X2,X4))) & r1_partfun1(X2,X3) & (k1_xboole_0 = X1 => k1_xboole_0 = X0))))),
% 0.21/0.52    inference(negated_conjecture,[],[f3])).
% 0.21/0.52  % (11526)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (11526)Memory used [KB]: 10618
% 0.21/0.52  % (11526)Time elapsed: 0.080 s
% 0.21/0.52  % (11526)------------------------------
% 0.21/0.52  % (11526)------------------------------
% 0.21/0.52  fof(f3,conjecture,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4)) => ~(r1_partfun1(X3,X4) & r1_partfun1(X2,X4))) & r1_partfun1(X2,X3) & (k1_xboole_0 = X1 => k1_xboole_0 = X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_2)).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    r1_partfun1(sK3,sK4(sK0,sK1,sK2,sK3)) | ~spl5_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f114])).
% 0.21/0.52  fof(f495,plain,(
% 0.21/0.52    ~spl5_1 | ~spl5_2 | ~spl5_3 | spl5_5 | ~spl5_6 | ~spl5_7 | spl5_30),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f494])).
% 0.21/0.52  fof(f494,plain,(
% 0.21/0.52    $false | (~spl5_1 | ~spl5_2 | ~spl5_3 | spl5_5 | ~spl5_6 | ~spl5_7 | spl5_30)),
% 0.21/0.52    inference(subsumption_resolution,[],[f493,f42])).
% 0.21/0.52  fof(f493,plain,(
% 0.21/0.52    ~v1_funct_1(sK2) | (~spl5_1 | ~spl5_3 | spl5_5 | ~spl5_6 | ~spl5_7 | spl5_30)),
% 0.21/0.52    inference(subsumption_resolution,[],[f492,f47])).
% 0.21/0.52  fof(f492,plain,(
% 0.21/0.52    ~r1_partfun1(sK2,sK3) | ~v1_funct_1(sK2) | (~spl5_1 | spl5_5 | ~spl5_6 | ~spl5_7 | spl5_30)),
% 0.21/0.52    inference(subsumption_resolution,[],[f491,f72])).
% 0.21/0.52  fof(f491,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | ~r1_partfun1(sK2,sK3) | ~v1_funct_1(sK2) | (~spl5_1 | ~spl5_6 | ~spl5_7 | spl5_30)),
% 0.21/0.52    inference(subsumption_resolution,[],[f490,f77])).
% 0.21/0.52  fof(f490,plain,(
% 0.21/0.52    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k1_xboole_0 = sK1 | ~r1_partfun1(sK2,sK3) | ~v1_funct_1(sK2) | (~spl5_1 | ~spl5_7 | spl5_30)),
% 0.21/0.52    inference(subsumption_resolution,[],[f489,f37])).
% 0.21/0.52  fof(f489,plain,(
% 0.21/0.52    ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k1_xboole_0 = sK1 | ~r1_partfun1(sK2,sK3) | ~v1_funct_1(sK2) | (~spl5_7 | spl5_30)),
% 0.21/0.52    inference(subsumption_resolution,[],[f488,f82])).
% 0.21/0.52  fof(f488,plain,(
% 0.21/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k1_xboole_0 = sK1 | ~r1_partfun1(sK2,sK3) | ~v1_funct_1(sK2) | spl5_30),
% 0.21/0.52    inference(resolution,[],[f486,f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r1_partfun1(X2,X3) | ~v1_funct_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f486,plain,(
% 0.21/0.52    ~m1_subset_1(sK4(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl5_30),
% 0.21/0.52    inference(avatar_component_clause,[],[f484])).
% 0.21/0.52  fof(f449,plain,(
% 0.21/0.52    spl5_26 | ~spl5_1 | ~spl5_2 | ~spl5_3 | spl5_5 | ~spl5_6 | ~spl5_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f435,f80,f75,f70,f45,f40,f35,f446])).
% 0.21/0.52  fof(f435,plain,(
% 0.21/0.52    r1_partfun1(sK2,sK4(sK0,sK1,sK2,sK3)) | (~spl5_1 | ~spl5_2 | ~spl5_3 | spl5_5 | ~spl5_6 | ~spl5_7)),
% 0.21/0.52    inference(subsumption_resolution,[],[f434,f37])).
% 0.21/0.52  fof(f434,plain,(
% 0.21/0.52    ~v1_funct_1(sK3) | r1_partfun1(sK2,sK4(sK0,sK1,sK2,sK3)) | (~spl5_2 | ~spl5_3 | spl5_5 | ~spl5_6 | ~spl5_7)),
% 0.21/0.52    inference(subsumption_resolution,[],[f431,f77])).
% 0.21/0.52  fof(f431,plain,(
% 0.21/0.52    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | r1_partfun1(sK2,sK4(sK0,sK1,sK2,sK3)) | (~spl5_2 | ~spl5_3 | spl5_5 | ~spl5_7)),
% 0.21/0.52    inference(resolution,[],[f263,f47])).
% 0.21/0.52  fof(f263,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_partfun1(sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0) | r1_partfun1(sK2,sK4(sK0,sK1,sK2,X0))) ) | (~spl5_2 | spl5_5 | ~spl5_7)),
% 0.21/0.52    inference(subsumption_resolution,[],[f102,f72])).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k1_xboole_0 = sK1 | ~r1_partfun1(sK2,X0) | r1_partfun1(sK2,sK4(sK0,sK1,sK2,X0))) ) | (~spl5_2 | ~spl5_7)),
% 0.21/0.52    inference(resolution,[],[f60,f82])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X10,X8,X9] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_1(X10) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | k1_xboole_0 = X9 | ~r1_partfun1(sK2,X10) | r1_partfun1(sK2,sK4(X8,X9,sK2,X10))) ) | ~spl5_2),
% 0.21/0.52    inference(resolution,[],[f42,f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r1_partfun1(X2,X3) | r1_partfun1(X2,sK4(X0,X1,X2,X3))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f442,plain,(
% 0.21/0.52    ~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_12 | ~spl5_13 | spl5_14),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f441])).
% 0.21/0.52  fof(f441,plain,(
% 0.21/0.52    $false | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_12 | ~spl5_13 | spl5_14)),
% 0.21/0.52    inference(subsumption_resolution,[],[f202,f197])).
% 0.21/0.52  fof(f197,plain,(
% 0.21/0.52    ~v1_funct_1(sK4(k1_xboole_0,sK1,sK2,sK3)) | spl5_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f196])).
% 0.21/0.52  fof(f196,plain,(
% 0.21/0.52    spl5_14 <=> v1_funct_1(sK4(k1_xboole_0,sK1,sK2,sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.52  fof(f202,plain,(
% 0.21/0.52    v1_funct_1(sK4(k1_xboole_0,sK1,sK2,sK3)) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_12 | ~spl5_13)),
% 0.21/0.52    inference(subsumption_resolution,[],[f201,f37])).
% 0.21/0.52  fof(f201,plain,(
% 0.21/0.52    ~v1_funct_1(sK3) | v1_funct_1(sK4(k1_xboole_0,sK1,sK2,sK3)) | (~spl5_2 | ~spl5_3 | ~spl5_12 | ~spl5_13)),
% 0.21/0.52    inference(subsumption_resolution,[],[f200,f172])).
% 0.21/0.52  fof(f172,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~spl5_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f170])).
% 0.21/0.52  % (11508)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.52  fof(f170,plain,(
% 0.21/0.52    spl5_12 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.52  fof(f200,plain,(
% 0.21/0.52    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~v1_funct_1(sK3) | v1_funct_1(sK4(k1_xboole_0,sK1,sK2,sK3)) | (~spl5_2 | ~spl5_3 | ~spl5_13)),
% 0.21/0.52    inference(resolution,[],[f184,f47])).
% 0.21/0.52  fof(f184,plain,(
% 0.21/0.52    ( ! [X2] : (~r1_partfun1(sK2,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~v1_funct_1(X2) | v1_funct_1(sK4(k1_xboole_0,sK1,sK2,X2))) ) | (~spl5_2 | ~spl5_13)),
% 0.21/0.52    inference(resolution,[],[f180,f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X19,X18] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18))) | ~v1_funct_1(X19) | ~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18))) | ~r1_partfun1(sK2,X19) | v1_funct_1(sK4(k1_xboole_0,X18,sK2,X19))) ) | ~spl5_2),
% 0.21/0.52    inference(resolution,[],[f42,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X2,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~r1_partfun1(X2,X3) | v1_funct_1(sK4(k1_xboole_0,X1,X2,X3))) )),
% 0.21/0.52    inference(equality_resolution,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | ~r1_partfun1(X2,X3) | v1_funct_1(sK4(X0,X1,X2,X3))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f180,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~spl5_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f178])).
% 0.21/0.52  fof(f178,plain,(
% 0.21/0.52    spl5_13 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.52  fof(f419,plain,(
% 0.21/0.52    ~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_12 | ~spl5_13 | spl5_25),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f418])).
% 0.21/0.52  fof(f418,plain,(
% 0.21/0.52    $false | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_12 | ~spl5_13 | spl5_25)),
% 0.21/0.52    inference(subsumption_resolution,[],[f417,f42])).
% 0.21/0.52  fof(f417,plain,(
% 0.21/0.52    ~v1_funct_1(sK2) | (~spl5_1 | ~spl5_3 | ~spl5_12 | ~spl5_13 | spl5_25)),
% 0.21/0.52    inference(subsumption_resolution,[],[f416,f47])).
% 0.21/0.52  fof(f416,plain,(
% 0.21/0.52    ~r1_partfun1(sK2,sK3) | ~v1_funct_1(sK2) | (~spl5_1 | ~spl5_12 | ~spl5_13 | spl5_25)),
% 0.21/0.52    inference(subsumption_resolution,[],[f415,f172])).
% 0.21/0.52  fof(f415,plain,(
% 0.21/0.52    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~r1_partfun1(sK2,sK3) | ~v1_funct_1(sK2) | (~spl5_1 | ~spl5_13 | spl5_25)),
% 0.21/0.52    inference(subsumption_resolution,[],[f414,f37])).
% 0.21/0.52  fof(f414,plain,(
% 0.21/0.52    ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~r1_partfun1(sK2,sK3) | ~v1_funct_1(sK2) | (~spl5_13 | spl5_25)),
% 0.21/0.52    inference(subsumption_resolution,[],[f412,f180])).
% 0.21/0.52  fof(f412,plain,(
% 0.21/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~r1_partfun1(sK2,sK3) | ~v1_funct_1(sK2) | spl5_25),
% 0.21/0.52    inference(resolution,[],[f404,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X2,X3,X1] : (v1_partfun1(sK4(k1_xboole_0,X1,X2,X3),k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~r1_partfun1(X2,X3) | ~v1_funct_1(X2)) )),
% 0.21/0.52    inference(equality_resolution,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | ~r1_partfun1(X2,X3) | v1_partfun1(sK4(X0,X1,X2,X3),X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f404,plain,(
% 0.21/0.52    ~v1_partfun1(sK4(k1_xboole_0,sK1,sK2,sK3),k1_xboole_0) | spl5_25),
% 0.21/0.52    inference(avatar_component_clause,[],[f402])).
% 0.21/0.52  fof(f402,plain,(
% 0.21/0.52    spl5_25 <=> v1_partfun1(sK4(k1_xboole_0,sK1,sK2,sK3),k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.21/0.52  fof(f405,plain,(
% 0.21/0.52    ~spl5_25 | ~spl5_14 | ~spl5_18 | spl5_20),
% 0.21/0.52    inference(avatar_split_clause,[],[f394,f343,f274,f196,f402])).
% 0.21/0.52  fof(f274,plain,(
% 0.21/0.52    spl5_18 <=> m1_subset_1(sK4(k1_xboole_0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.52  fof(f343,plain,(
% 0.21/0.52    spl5_20 <=> v1_funct_2(sK4(k1_xboole_0,sK1,sK2,sK3),k1_xboole_0,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.52  fof(f394,plain,(
% 0.21/0.52    ~v1_partfun1(sK4(k1_xboole_0,sK1,sK2,sK3),k1_xboole_0) | (~spl5_14 | ~spl5_18 | spl5_20)),
% 0.21/0.52    inference(subsumption_resolution,[],[f393,f275])).
% 0.21/0.52  fof(f275,plain,(
% 0.21/0.52    m1_subset_1(sK4(k1_xboole_0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~spl5_18),
% 0.21/0.52    inference(avatar_component_clause,[],[f274])).
% 0.21/0.52  fof(f393,plain,(
% 0.21/0.52    ~v1_partfun1(sK4(k1_xboole_0,sK1,sK2,sK3),k1_xboole_0) | ~m1_subset_1(sK4(k1_xboole_0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl5_14 | spl5_20)),
% 0.21/0.52    inference(resolution,[],[f203,f345])).
% 0.21/0.52  fof(f345,plain,(
% 0.21/0.52    ~v1_funct_2(sK4(k1_xboole_0,sK1,sK2,sK3),k1_xboole_0,sK1) | spl5_20),
% 0.21/0.52    inference(avatar_component_clause,[],[f343])).
% 0.21/0.52  fof(f203,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_funct_2(sK4(k1_xboole_0,sK1,sK2,sK3),X0,X1) | ~v1_partfun1(sK4(k1_xboole_0,sK1,sK2,sK3),X0) | ~m1_subset_1(sK4(k1_xboole_0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl5_14),
% 0.21/0.52    inference(resolution,[],[f198,f18])).
% 0.21/0.52  fof(f198,plain,(
% 0.21/0.52    v1_funct_1(sK4(k1_xboole_0,sK1,sK2,sK3)) | ~spl5_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f196])).
% 0.21/0.52  fof(f355,plain,(
% 0.21/0.52    ~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_12 | ~spl5_13 | spl5_21),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f354])).
% 0.21/0.52  fof(f354,plain,(
% 0.21/0.52    $false | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_12 | ~spl5_13 | spl5_21)),
% 0.21/0.52    inference(subsumption_resolution,[],[f353,f37])).
% 0.21/0.52  fof(f353,plain,(
% 0.21/0.52    ~v1_funct_1(sK3) | (~spl5_2 | ~spl5_3 | ~spl5_12 | ~spl5_13 | spl5_21)),
% 0.21/0.52    inference(subsumption_resolution,[],[f352,f47])).
% 0.21/0.52  fof(f352,plain,(
% 0.21/0.52    ~r1_partfun1(sK2,sK3) | ~v1_funct_1(sK3) | (~spl5_2 | ~spl5_12 | ~spl5_13 | spl5_21)),
% 0.21/0.52    inference(subsumption_resolution,[],[f351,f172])).
% 0.21/0.52  fof(f351,plain,(
% 0.21/0.52    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~r1_partfun1(sK2,sK3) | ~v1_funct_1(sK3) | (~spl5_2 | ~spl5_13 | spl5_21)),
% 0.21/0.52    inference(resolution,[],[f349,f182])).
% 0.21/0.52  fof(f182,plain,(
% 0.21/0.52    ( ! [X0] : (r1_partfun1(sK2,sK4(k1_xboole_0,sK1,sK2,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~r1_partfun1(sK2,X0) | ~v1_funct_1(X0)) ) | (~spl5_2 | ~spl5_13)),
% 0.21/0.52    inference(resolution,[],[f180,f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X17,X16] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X16))) | ~v1_funct_1(X17) | ~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X16))) | ~r1_partfun1(sK2,X17) | r1_partfun1(sK2,sK4(k1_xboole_0,X16,sK2,X17))) ) | ~spl5_2),
% 0.21/0.52    inference(resolution,[],[f42,f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X2,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~r1_partfun1(X2,X3) | r1_partfun1(X2,sK4(k1_xboole_0,X1,X2,X3))) )),
% 0.21/0.52    inference(equality_resolution,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | ~r1_partfun1(X2,X3) | r1_partfun1(X2,sK4(X0,X1,X2,X3))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f349,plain,(
% 0.21/0.52    ~r1_partfun1(sK2,sK4(k1_xboole_0,sK1,sK2,sK3)) | spl5_21),
% 0.21/0.52    inference(avatar_component_clause,[],[f347])).
% 0.21/0.52  fof(f347,plain,(
% 0.21/0.52    spl5_21 <=> r1_partfun1(sK2,sK4(k1_xboole_0,sK1,sK2,sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.52  fof(f350,plain,(
% 0.21/0.52    ~spl5_20 | ~spl5_21 | ~spl5_4 | ~spl5_8 | ~spl5_9 | ~spl5_18),
% 0.21/0.52    inference(avatar_split_clause,[],[f341,f274,f114,f90,f66,f347,f343])).
% 0.21/0.52  fof(f341,plain,(
% 0.21/0.52    ~r1_partfun1(sK2,sK4(k1_xboole_0,sK1,sK2,sK3)) | ~v1_funct_2(sK4(k1_xboole_0,sK1,sK2,sK3),k1_xboole_0,sK1) | (~spl5_4 | ~spl5_8 | ~spl5_9 | ~spl5_18)),
% 0.21/0.52    inference(forward_demodulation,[],[f340,f68])).
% 0.21/0.52  fof(f340,plain,(
% 0.21/0.52    ~v1_funct_2(sK4(k1_xboole_0,sK1,sK2,sK3),k1_xboole_0,sK1) | ~r1_partfun1(sK2,sK4(sK0,sK1,sK2,sK3)) | (~spl5_4 | ~spl5_8 | ~spl5_9 | ~spl5_18)),
% 0.21/0.52    inference(subsumption_resolution,[],[f339,f275])).
% 0.21/0.52  fof(f339,plain,(
% 0.21/0.52    ~m1_subset_1(sK4(k1_xboole_0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~v1_funct_2(sK4(k1_xboole_0,sK1,sK2,sK3),k1_xboole_0,sK1) | ~r1_partfun1(sK2,sK4(sK0,sK1,sK2,sK3)) | (~spl5_4 | ~spl5_8 | ~spl5_9)),
% 0.21/0.52    inference(forward_demodulation,[],[f338,f68])).
% 0.21/0.52  fof(f338,plain,(
% 0.21/0.52    ~v1_funct_2(sK4(k1_xboole_0,sK1,sK2,sK3),k1_xboole_0,sK1) | ~m1_subset_1(sK4(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r1_partfun1(sK2,sK4(sK0,sK1,sK2,sK3)) | (~spl5_4 | ~spl5_8 | ~spl5_9)),
% 0.21/0.52    inference(forward_demodulation,[],[f127,f68])).
% 0.21/0.53  fof(f294,plain,(
% 0.21/0.53    ~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_12 | ~spl5_13 | spl5_18),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f293])).
% 0.21/0.53  fof(f293,plain,(
% 0.21/0.53    $false | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_12 | ~spl5_13 | spl5_18)),
% 0.21/0.53    inference(subsumption_resolution,[],[f292,f42])).
% 0.21/0.53  fof(f292,plain,(
% 0.21/0.53    ~v1_funct_1(sK2) | (~spl5_1 | ~spl5_3 | ~spl5_12 | ~spl5_13 | spl5_18)),
% 0.21/0.53    inference(subsumption_resolution,[],[f291,f47])).
% 0.21/0.53  fof(f291,plain,(
% 0.21/0.53    ~r1_partfun1(sK2,sK3) | ~v1_funct_1(sK2) | (~spl5_1 | ~spl5_12 | ~spl5_13 | spl5_18)),
% 0.21/0.53    inference(subsumption_resolution,[],[f290,f172])).
% 0.21/0.53  fof(f290,plain,(
% 0.21/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~r1_partfun1(sK2,sK3) | ~v1_funct_1(sK2) | (~spl5_1 | ~spl5_13 | spl5_18)),
% 0.21/0.53    inference(subsumption_resolution,[],[f289,f37])).
% 0.21/0.53  fof(f289,plain,(
% 0.21/0.53    ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~r1_partfun1(sK2,sK3) | ~v1_funct_1(sK2) | (~spl5_13 | spl5_18)),
% 0.21/0.53    inference(subsumption_resolution,[],[f287,f180])).
% 0.21/0.53  fof(f287,plain,(
% 0.21/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~r1_partfun1(sK2,sK3) | ~v1_funct_1(sK2) | spl5_18),
% 0.21/0.53    inference(resolution,[],[f276,f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ( ! [X2,X3,X1] : (m1_subset_1(sK4(k1_xboole_0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~r1_partfun1(X2,X3) | ~v1_funct_1(X2)) )),
% 0.21/0.53    inference(equality_resolution,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | ~r1_partfun1(X2,X3) | m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f276,plain,(
% 0.21/0.53    ~m1_subset_1(sK4(k1_xboole_0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | spl5_18),
% 0.21/0.53    inference(avatar_component_clause,[],[f274])).
% 0.21/0.53  fof(f181,plain,(
% 0.21/0.53    spl5_13 | ~spl5_4 | ~spl5_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f144,f80,f66,f178])).
% 0.21/0.53  fof(f144,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl5_4 | ~spl5_7)),
% 0.21/0.53    inference(superposition,[],[f82,f68])).
% 0.21/0.53  fof(f173,plain,(
% 0.21/0.53    spl5_12 | ~spl5_4 | ~spl5_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f143,f75,f66,f170])).
% 0.21/0.53  fof(f143,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl5_4 | ~spl5_6)),
% 0.21/0.53    inference(superposition,[],[f77,f68])).
% 0.21/0.53  fof(f167,plain,(
% 0.21/0.53    spl5_11 | ~spl5_4 | ~spl5_5 | ~spl5_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f153,f75,f70,f66,f164])).
% 0.21/0.53  fof(f153,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.21/0.53    inference(forward_demodulation,[],[f148,f68])).
% 0.21/0.53  fof(f148,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl5_5 | ~spl5_6)),
% 0.21/0.53    inference(superposition,[],[f77,f71])).
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    spl5_9 | ~spl5_1 | ~spl5_2 | ~spl5_3 | spl5_5 | ~spl5_6 | ~spl5_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f111,f80,f75,f70,f45,f40,f35,f114])).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    r1_partfun1(sK3,sK4(sK0,sK1,sK2,sK3)) | (~spl5_1 | ~spl5_2 | ~spl5_3 | spl5_5 | ~spl5_6 | ~spl5_7)),
% 0.21/0.53    inference(subsumption_resolution,[],[f110,f37])).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    ~v1_funct_1(sK3) | r1_partfun1(sK3,sK4(sK0,sK1,sK2,sK3)) | (~spl5_2 | ~spl5_3 | spl5_5 | ~spl5_6 | ~spl5_7)),
% 0.21/0.53    inference(subsumption_resolution,[],[f108,f77])).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | r1_partfun1(sK3,sK4(sK0,sK1,sK2,sK3)) | (~spl5_2 | ~spl5_3 | spl5_5 | ~spl5_7)),
% 0.21/0.53    inference(resolution,[],[f107,f47])).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_partfun1(sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0) | r1_partfun1(X0,sK4(sK0,sK1,sK2,X0))) ) | (~spl5_2 | spl5_5 | ~spl5_7)),
% 0.21/0.53    inference(subsumption_resolution,[],[f106,f72])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k1_xboole_0 = sK1 | ~r1_partfun1(sK2,X0) | r1_partfun1(X0,sK4(sK0,sK1,sK2,X0))) ) | (~spl5_2 | ~spl5_7)),
% 0.21/0.53    inference(resolution,[],[f61,f82])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X12,X13,X11] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) | ~v1_funct_1(X13) | ~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) | k1_xboole_0 = X12 | ~r1_partfun1(sK2,X13) | r1_partfun1(X13,sK4(X11,X12,sK2,X13))) ) | ~spl5_2),
% 0.21/0.53    inference(resolution,[],[f42,f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r1_partfun1(X2,X3) | r1_partfun1(X3,sK4(X0,X1,X2,X3))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    spl5_8 | ~spl5_1 | ~spl5_2 | ~spl5_3 | spl5_5 | ~spl5_6 | ~spl5_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f88,f80,f75,f70,f45,f40,f35,f90])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    v1_funct_1(sK4(sK0,sK1,sK2,sK3)) | (~spl5_1 | ~spl5_2 | ~spl5_3 | spl5_5 | ~spl5_6 | ~spl5_7)),
% 0.21/0.53    inference(subsumption_resolution,[],[f87,f37])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    ~v1_funct_1(sK3) | v1_funct_1(sK4(sK0,sK1,sK2,sK3)) | (~spl5_2 | ~spl5_3 | spl5_5 | ~spl5_6 | ~spl5_7)),
% 0.21/0.53    inference(subsumption_resolution,[],[f86,f77])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | v1_funct_1(sK4(sK0,sK1,sK2,sK3)) | (~spl5_2 | ~spl5_3 | spl5_5 | ~spl5_7)),
% 0.21/0.53    inference(resolution,[],[f85,f47])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_partfun1(sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0) | v1_funct_1(sK4(sK0,sK1,sK2,X0))) ) | (~spl5_2 | spl5_5 | ~spl5_7)),
% 0.21/0.53    inference(subsumption_resolution,[],[f84,f72])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k1_xboole_0 = sK1 | ~r1_partfun1(sK2,X0) | v1_funct_1(sK4(sK0,sK1,sK2,X0))) ) | (~spl5_2 | ~spl5_7)),
% 0.21/0.53    inference(resolution,[],[f58,f82])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X4,X2,X3] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_xboole_0 = X3 | ~r1_partfun1(sK2,X4) | v1_funct_1(sK4(X2,X3,sK2,X4))) ) | ~spl5_2),
% 0.21/0.53    inference(resolution,[],[f42,f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r1_partfun1(X2,X3) | v1_funct_1(sK4(X0,X1,X2,X3))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    spl5_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f17,f80])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    spl5_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f14,f75])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    spl5_4 | ~spl5_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f12,f70,f66])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    spl5_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f15,f45])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    r1_partfun1(sK2,sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    spl5_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f16,f40])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    v1_funct_1(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    spl5_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f13,f35])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    v1_funct_1(sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (11509)------------------------------
% 0.21/0.53  % (11509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (11509)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (11509)Memory used [KB]: 11001
% 0.21/0.53  % (11509)Time elapsed: 0.088 s
% 0.21/0.53  % (11509)------------------------------
% 0.21/0.53  % (11509)------------------------------
% 0.21/0.53  % (11505)Success in time 0.163 s
%------------------------------------------------------------------------------
