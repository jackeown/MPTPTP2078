%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  223 ( 914 expanded)
%              Number of leaves         :   23 ( 186 expanded)
%              Depth                    :   28
%              Number of atoms          : 1304 (8603 expanded)
%              Number of equality atoms :  153 (1544 expanded)
%              Maximal formula depth    :   26 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f531,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f92,f172,f205,f272,f298,f302,f312,f401,f445,f451,f485,f520])).

fof(f520,plain,
    ( spl6_1
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_20
    | ~ spl6_28 ),
    inference(avatar_contradiction_clause,[],[f519])).

fof(f519,plain,
    ( $false
    | spl6_1
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_20
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f518,f453])).

fof(f453,plain,
    ( k1_xboole_0 = k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
    | ~ spl6_3
    | ~ spl6_28 ),
    inference(backward_demodulation,[],[f428,f442])).

fof(f442,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f440])).

fof(f440,plain,
    ( spl6_28
  <=> k1_xboole_0 = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f428,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f321,f424])).

fof(f424,plain,
    ( k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f423,f42])).

fof(f42,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
                            | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
                            | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & r1_subset_1(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(X0))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
                            | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
                            | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & r1_subset_1(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(X0))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                      & ~ v1_xboole_0(X3) )
                   => ( r1_subset_1(X2,X3)
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                            & v1_funct_2(X4,X2,X1)
                            & v1_funct_1(X4) )
                         => ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                                & v1_funct_2(X5,X3,X1)
                                & v1_funct_1(X5) )
                             => ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5
                                & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4
                                & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
                & ~ v1_xboole_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                 => ( r1_subset_1(X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                          & v1_funct_2(X4,X2,X1)
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                              & v1_funct_2(X5,X3,X1)
                              & v1_funct_1(X5) )
                           => ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5
                              & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4
                              & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tmap_1)).

fof(f423,plain,
    ( k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(sK4)
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f419,f44])).

fof(f44,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f419,plain,
    ( k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | ~ spl6_3 ),
    inference(superposition,[],[f321,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f321,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f320,f39])).

fof(f39,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f19])).

fof(f320,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(sK5)
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f315,f41])).

fof(f41,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f315,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ spl6_3 ),
    inference(superposition,[],[f90,f71])).

fof(f90,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl6_3
  <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f518,plain,
    ( k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
    | spl6_1
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_20
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f517,f152])).

fof(f152,plain,
    ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl6_11
  <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f517,plain,
    ( ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
    | spl6_1
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_20
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f516,f241])).

fof(f241,plain,
    ( v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl6_20
  <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f516,plain,
    ( ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
    | spl6_1
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f515,f148])).

fof(f148,plain,
    ( v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl6_10
  <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f515,plain,
    ( ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
    | spl6_1
    | ~ spl6_3
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f514,f44])).

fof(f514,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
    | spl6_1
    | ~ spl6_3
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f513,f43])).

fof(f43,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f513,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
    | spl6_1
    | ~ spl6_3
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f511,f42])).

fof(f511,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
    | spl6_1
    | ~ spl6_3
    | ~ spl6_28 ),
    inference(trivial_inequality_removal,[],[f506])).

fof(f506,plain,
    ( sK5 != sK5
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
    | spl6_1
    | ~ spl6_3
    | ~ spl6_28 ),
    inference(superposition,[],[f83,f456])).

fof(f456,plain,
    ( ! [X1] :
        ( sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5))
        | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | k1_xboole_0 != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3)) )
    | ~ spl6_3
    | ~ spl6_28 ),
    inference(backward_demodulation,[],[f425,f442])).

fof(f425,plain,
    ( ! [X1] :
        ( k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5))
        | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3) )
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f342,f424])).

fof(f342,plain,
    ( ! [X1] :
        ( k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5))
        | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3) )
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f341,f321])).

fof(f341,plain,
    ( ! [X1] :
        ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5))
        | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3) )
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f340,f51])).

fof(f51,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f340,plain,
    ( ! [X1] :
        ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | v1_xboole_0(sK0)
        | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5))
        | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3) )
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f339,f41])).

fof(f339,plain,
    ( ! [X1] :
        ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
        | v1_xboole_0(sK0)
        | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5))
        | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3) )
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f338,f40])).

fof(f40,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f338,plain,
    ( ! [X1] :
        ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(sK5,sK3,sK1)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
        | v1_xboole_0(sK0)
        | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5))
        | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3) )
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f337,f39])).

fof(f337,plain,
    ( ! [X1] :
        ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,sK3,sK1)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
        | v1_xboole_0(sK0)
        | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5))
        | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3) )
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f336,f46])).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f336,plain,
    ( ! [X1] :
        ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,sK3,sK1)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
        | v1_xboole_0(sK0)
        | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5))
        | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3) )
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f335,f45])).

fof(f45,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f335,plain,
    ( ! [X1] :
        ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3))
        | v1_xboole_0(sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,sK3,sK1)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
        | v1_xboole_0(sK0)
        | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5))
        | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3) )
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f334,f49])).

fof(f49,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f334,plain,
    ( ! [X1] :
        ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
        | v1_xboole_0(sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,sK3,sK1)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
        | v1_xboole_0(sK0)
        | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5))
        | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3) )
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f333,f48])).

fof(f48,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f333,plain,
    ( ! [X1] :
        ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3))
        | v1_xboole_0(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
        | v1_xboole_0(sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,sK3,sK1)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
        | v1_xboole_0(sK0)
        | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5))
        | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3) )
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f317,f50])).

fof(f50,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f317,plain,
    ( ! [X1] :
        ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3))
        | v1_xboole_0(sK1)
        | v1_xboole_0(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
        | v1_xboole_0(sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,sK3,sK1)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
        | v1_xboole_0(sK0)
        | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5))
        | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3) )
    | ~ spl6_3 ),
    inference(superposition,[],[f77,f90])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | v1_xboole_0(X0)
      | ~ v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | ~ v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
      | ~ m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
      | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                              <=> ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                  & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                              | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                              | ~ v1_funct_1(X6) )
                          | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          | ~ v1_funct_2(X5,X3,X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      | ~ v1_funct_2(X4,X2,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                              <=> ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                  & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                              | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                              | ~ v1_funct_1(X6) )
                          | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          | ~ v1_funct_2(X5,X3,X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      | ~ v1_funct_2(X4,X2,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
                & ~ v1_xboole_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                        & v1_funct_2(X4,X2,X1)
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                            & v1_funct_2(X5,X3,X1)
                            & v1_funct_1(X5) )
                         => ( k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                           => ! [X6] :
                                ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                                  & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                                  & v1_funct_1(X6) )
                               => ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                <=> ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                    & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tmap_1)).

fof(f83,plain,
    ( sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl6_1
  <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f485,plain,
    ( spl6_2
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_20
    | ~ spl6_28 ),
    inference(avatar_contradiction_clause,[],[f484])).

fof(f484,plain,
    ( $false
    | spl6_2
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_20
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f483,f453])).

fof(f483,plain,
    ( k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_20
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f482,f152])).

fof(f482,plain,
    ( ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_20
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f481,f241])).

fof(f481,plain,
    ( ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f480,f148])).

fof(f480,plain,
    ( ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f479,f44])).

fof(f479,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f478,f43])).

fof(f478,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f476,f42])).

fof(f476,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_28 ),
    inference(trivial_inequality_removal,[],[f473])).

fof(f473,plain,
    ( sK4 != sK4
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_28 ),
    inference(superposition,[],[f87,f455])).

fof(f455,plain,
    ( ! [X0] :
        ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),sK2) = X0
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK2,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5))
        | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | k1_xboole_0 != k2_partfun1(sK2,sK1,X0,k9_subset_1(sK0,sK2,sK3)) )
    | ~ spl6_3
    | ~ spl6_28 ),
    inference(backward_demodulation,[],[f426,f442])).

fof(f426,plain,
    ( ! [X0] :
        ( k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X0,k9_subset_1(sK0,sK2,sK3))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK2,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5))
        | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),sK2) = X0 )
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f332,f424])).

fof(f332,plain,
    ( ! [X0] :
        ( k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X0,k9_subset_1(sK0,sK2,sK3))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK2,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5))
        | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),sK2) = X0 )
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f331,f321])).

fof(f331,plain,
    ( ! [X0] :
        ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X0,k9_subset_1(sK0,sK2,sK3))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK2,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5))
        | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),sK2) = X0 )
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f330,f51])).

fof(f330,plain,
    ( ! [X0] :
        ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X0,k9_subset_1(sK0,sK2,sK3))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK2,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | v1_xboole_0(sK0)
        | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5))
        | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),sK2) = X0 )
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f329,f41])).

fof(f329,plain,
    ( ! [X0] :
        ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X0,k9_subset_1(sK0,sK2,sK3))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK2,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
        | v1_xboole_0(sK0)
        | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5))
        | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),sK2) = X0 )
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f328,f40])).

fof(f328,plain,
    ( ! [X0] :
        ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X0,k9_subset_1(sK0,sK2,sK3))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK2,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(sK5,sK3,sK1)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
        | v1_xboole_0(sK0)
        | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5))
        | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),sK2) = X0 )
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f327,f39])).

fof(f327,plain,
    ( ! [X0] :
        ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X0,k9_subset_1(sK0,sK2,sK3))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK2,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,sK3,sK1)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
        | v1_xboole_0(sK0)
        | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5))
        | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),sK2) = X0 )
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f326,f46])).

fof(f326,plain,
    ( ! [X0] :
        ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X0,k9_subset_1(sK0,sK2,sK3))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK2,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,sK3,sK1)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
        | v1_xboole_0(sK0)
        | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5))
        | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),sK2) = X0 )
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f325,f45])).

fof(f325,plain,
    ( ! [X0] :
        ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X0,k9_subset_1(sK0,sK2,sK3))
        | v1_xboole_0(sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK2,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,sK3,sK1)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
        | v1_xboole_0(sK0)
        | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5))
        | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),sK2) = X0 )
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f324,f49])).

fof(f324,plain,
    ( ! [X0] :
        ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X0,k9_subset_1(sK0,sK2,sK3))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
        | v1_xboole_0(sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK2,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,sK3,sK1)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
        | v1_xboole_0(sK0)
        | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5))
        | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),sK2) = X0 )
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f323,f48])).

fof(f323,plain,
    ( ! [X0] :
        ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X0,k9_subset_1(sK0,sK2,sK3))
        | v1_xboole_0(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
        | v1_xboole_0(sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK2,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,sK3,sK1)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
        | v1_xboole_0(sK0)
        | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5))
        | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),sK2) = X0 )
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f316,f50])).

fof(f316,plain,
    ( ! [X0] :
        ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X0,k9_subset_1(sK0,sK2,sK3))
        | v1_xboole_0(sK1)
        | v1_xboole_0(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
        | v1_xboole_0(sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK2,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,sK3,sK1)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
        | v1_xboole_0(sK0)
        | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5))
        | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),sK2) = X0 )
    | ~ spl6_3 ),
    inference(superposition,[],[f78,f90])).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | v1_xboole_0(X0)
      | ~ v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | ~ v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
      | ~ m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4
      | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f87,plain,
    ( sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl6_2
  <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f451,plain,
    ( ~ spl6_25
    | spl6_27 ),
    inference(avatar_contradiction_clause,[],[f450])).

fof(f450,plain,
    ( $false
    | ~ spl6_25
    | spl6_27 ),
    inference(subsumption_resolution,[],[f449,f46])).

fof(f449,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl6_25
    | spl6_27 ),
    inference(subsumption_resolution,[],[f447,f387])).

fof(f387,plain,
    ( r1_xboole_0(k3_xboole_0(sK2,sK3),k1_relat_1(sK5))
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f386])).

fof(f386,plain,
    ( spl6_25
  <=> r1_xboole_0(k3_xboole_0(sK2,sK3),k1_relat_1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f447,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK2,sK3),k1_relat_1(sK5))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | spl6_27 ),
    inference(superposition,[],[f438,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f438,plain,
    ( ~ r1_xboole_0(k9_subset_1(sK0,sK2,sK3),k1_relat_1(sK5))
    | spl6_27 ),
    inference(avatar_component_clause,[],[f436])).

fof(f436,plain,
    ( spl6_27
  <=> r1_xboole_0(k9_subset_1(sK0,sK2,sK3),k1_relat_1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f445,plain,
    ( ~ spl6_27
    | spl6_28
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f444,f89,f440,f436])).

fof(f444,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | ~ r1_xboole_0(k9_subset_1(sK0,sK2,sK3),k1_relat_1(sK5))
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f431,f126])).

fof(f126,plain,(
    v1_relat_1(sK5) ),
    inference(subsumption_resolution,[],[f113,f59])).

fof(f59,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f113,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK3,sK1))
    | v1_relat_1(sK5) ),
    inference(resolution,[],[f41,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f431,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | ~ r1_xboole_0(k9_subset_1(sK0,sK2,sK3),k1_relat_1(sK5))
    | ~ v1_relat_1(sK5)
    | ~ spl6_3 ),
    inference(superposition,[],[f56,f424])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

fof(f401,plain,
    ( ~ spl6_23
    | spl6_25 ),
    inference(avatar_contradiction_clause,[],[f400])).

fof(f400,plain,
    ( $false
    | ~ spl6_23
    | spl6_25 ),
    inference(subsumption_resolution,[],[f399,f95])).

fof(f95,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f94,f48])).

fof(f94,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f93,f45])).

fof(f93,plain,
    ( v1_xboole_0(sK3)
    | r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f47,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r1_xboole_0(X0,X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(f47,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f399,plain,
    ( ~ r1_xboole_0(sK2,sK3)
    | ~ spl6_23
    | spl6_25 ),
    inference(subsumption_resolution,[],[f397,f292])).

fof(f292,plain,
    ( r1_xboole_0(k1_xboole_0,k1_relat_1(sK5))
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f291])).

fof(f291,plain,
    ( spl6_23
  <=> r1_xboole_0(k1_xboole_0,k1_relat_1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f397,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK5))
    | ~ r1_xboole_0(sK2,sK3)
    | spl6_25 ),
    inference(superposition,[],[f388,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f388,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK2,sK3),k1_relat_1(sK5))
    | spl6_25 ),
    inference(avatar_component_clause,[],[f386])).

fof(f312,plain,(
    spl6_24 ),
    inference(avatar_contradiction_clause,[],[f311])).

fof(f311,plain,
    ( $false
    | spl6_24 ),
    inference(subsumption_resolution,[],[f309,f52])).

fof(f52,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f309,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK4),k1_xboole_0)
    | spl6_24 ),
    inference(resolution,[],[f308,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f308,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK4))
    | spl6_24 ),
    inference(subsumption_resolution,[],[f307,f144])).

fof(f144,plain,(
    v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f131,f59])).

fof(f131,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK1))
    | v1_relat_1(sK4) ),
    inference(resolution,[],[f44,f57])).

fof(f307,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | spl6_24 ),
    inference(trivial_inequality_removal,[],[f306])).

fof(f306,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | spl6_24 ),
    inference(superposition,[],[f297,f56])).

fof(f297,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | spl6_24 ),
    inference(avatar_component_clause,[],[f295])).

fof(f295,plain,
    ( spl6_24
  <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f302,plain,(
    spl6_23 ),
    inference(avatar_contradiction_clause,[],[f301])).

fof(f301,plain,
    ( $false
    | spl6_23 ),
    inference(subsumption_resolution,[],[f299,f52])).

fof(f299,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK5),k1_xboole_0)
    | spl6_23 ),
    inference(resolution,[],[f293,f61])).

fof(f293,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK5))
    | spl6_23 ),
    inference(avatar_component_clause,[],[f291])).

fof(f298,plain,
    ( ~ spl6_23
    | ~ spl6_24
    | spl6_3 ),
    inference(avatar_split_clause,[],[f289,f89,f295,f291])).

fof(f289,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK5))
    | spl6_3 ),
    inference(subsumption_resolution,[],[f288,f126])).

fof(f288,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK5))
    | ~ v1_relat_1(sK5)
    | spl6_3 ),
    inference(superposition,[],[f287,f56])).

fof(f287,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
    | spl6_3 ),
    inference(subsumption_resolution,[],[f286,f42])).

fof(f286,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
    | ~ v1_funct_1(sK4)
    | spl6_3 ),
    inference(subsumption_resolution,[],[f285,f44])).

fof(f285,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | spl6_3 ),
    inference(superposition,[],[f284,f71])).

fof(f284,plain,
    ( k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | spl6_3 ),
    inference(subsumption_resolution,[],[f283,f39])).

fof(f283,plain,
    ( k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | ~ v1_funct_1(sK5)
    | spl6_3 ),
    inference(subsumption_resolution,[],[f282,f41])).

fof(f282,plain,
    ( k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | spl6_3 ),
    inference(superposition,[],[f275,f71])).

fof(f275,plain,
    ( k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0)
    | spl6_3 ),
    inference(subsumption_resolution,[],[f273,f95])).

fof(f273,plain,
    ( k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0)
    | ~ r1_xboole_0(sK2,sK3)
    | spl6_3 ),
    inference(superposition,[],[f256,f67])).

fof(f256,plain,
    ( k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3))
    | spl6_3 ),
    inference(subsumption_resolution,[],[f254,f46])).

fof(f254,plain,
    ( k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | spl6_3 ),
    inference(superposition,[],[f91,f68])).

fof(f91,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f272,plain,(
    spl6_20 ),
    inference(avatar_contradiction_clause,[],[f271])).

fof(f271,plain,
    ( $false
    | spl6_20 ),
    inference(subsumption_resolution,[],[f270,f51])).

fof(f270,plain,
    ( v1_xboole_0(sK0)
    | spl6_20 ),
    inference(subsumption_resolution,[],[f269,f41])).

fof(f269,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_xboole_0(sK0)
    | spl6_20 ),
    inference(subsumption_resolution,[],[f268,f40])).

fof(f268,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_xboole_0(sK0)
    | spl6_20 ),
    inference(subsumption_resolution,[],[f267,f39])).

fof(f267,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_xboole_0(sK0)
    | spl6_20 ),
    inference(subsumption_resolution,[],[f266,f44])).

fof(f266,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_xboole_0(sK0)
    | spl6_20 ),
    inference(subsumption_resolution,[],[f265,f43])).

fof(f265,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_xboole_0(sK0)
    | spl6_20 ),
    inference(subsumption_resolution,[],[f264,f42])).

fof(f264,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_xboole_0(sK0)
    | spl6_20 ),
    inference(subsumption_resolution,[],[f263,f46])).

fof(f263,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_xboole_0(sK0)
    | spl6_20 ),
    inference(subsumption_resolution,[],[f262,f45])).

fof(f262,plain,
    ( v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_xboole_0(sK0)
    | spl6_20 ),
    inference(subsumption_resolution,[],[f261,f49])).

fof(f261,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_xboole_0(sK0)
    | spl6_20 ),
    inference(subsumption_resolution,[],[f260,f48])).

fof(f260,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_xboole_0(sK0)
    | spl6_20 ),
    inference(subsumption_resolution,[],[f259,f50])).

fof(f259,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_xboole_0(sK0)
    | spl6_20 ),
    inference(resolution,[],[f242,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
        & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
        & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
        & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
        & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
        & v1_funct_2(X5,X3,X1)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(X4,X2,X1)
        & v1_funct_1(X4)
        & m1_subset_1(X3,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
        & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
        & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tmap_1)).

fof(f242,plain,
    ( ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | spl6_20 ),
    inference(avatar_component_clause,[],[f240])).

fof(f205,plain,(
    spl6_11 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | spl6_11 ),
    inference(subsumption_resolution,[],[f203,f51])).

fof(f203,plain,
    ( v1_xboole_0(sK0)
    | spl6_11 ),
    inference(subsumption_resolution,[],[f202,f41])).

fof(f202,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_xboole_0(sK0)
    | spl6_11 ),
    inference(subsumption_resolution,[],[f201,f40])).

fof(f201,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_xboole_0(sK0)
    | spl6_11 ),
    inference(subsumption_resolution,[],[f200,f39])).

fof(f200,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_xboole_0(sK0)
    | spl6_11 ),
    inference(subsumption_resolution,[],[f199,f44])).

fof(f199,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_xboole_0(sK0)
    | spl6_11 ),
    inference(subsumption_resolution,[],[f198,f43])).

fof(f198,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_xboole_0(sK0)
    | spl6_11 ),
    inference(subsumption_resolution,[],[f197,f42])).

fof(f197,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_xboole_0(sK0)
    | spl6_11 ),
    inference(subsumption_resolution,[],[f196,f46])).

fof(f196,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_xboole_0(sK0)
    | spl6_11 ),
    inference(subsumption_resolution,[],[f195,f45])).

fof(f195,plain,
    ( v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_xboole_0(sK0)
    | spl6_11 ),
    inference(subsumption_resolution,[],[f194,f49])).

fof(f194,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_xboole_0(sK0)
    | spl6_11 ),
    inference(subsumption_resolution,[],[f193,f48])).

fof(f193,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_xboole_0(sK0)
    | spl6_11 ),
    inference(subsumption_resolution,[],[f192,f50])).

fof(f192,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_xboole_0(sK0)
    | spl6_11 ),
    inference(resolution,[],[f153,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f153,plain,
    ( ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | spl6_11 ),
    inference(avatar_component_clause,[],[f151])).

fof(f172,plain,(
    spl6_10 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | spl6_10 ),
    inference(subsumption_resolution,[],[f170,f51])).

fof(f170,plain,
    ( v1_xboole_0(sK0)
    | spl6_10 ),
    inference(subsumption_resolution,[],[f169,f41])).

fof(f169,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_xboole_0(sK0)
    | spl6_10 ),
    inference(subsumption_resolution,[],[f168,f40])).

fof(f168,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_xboole_0(sK0)
    | spl6_10 ),
    inference(subsumption_resolution,[],[f167,f39])).

fof(f167,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_xboole_0(sK0)
    | spl6_10 ),
    inference(subsumption_resolution,[],[f166,f44])).

fof(f166,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_xboole_0(sK0)
    | spl6_10 ),
    inference(subsumption_resolution,[],[f165,f43])).

fof(f165,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_xboole_0(sK0)
    | spl6_10 ),
    inference(subsumption_resolution,[],[f164,f42])).

fof(f164,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_xboole_0(sK0)
    | spl6_10 ),
    inference(subsumption_resolution,[],[f163,f46])).

fof(f163,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_xboole_0(sK0)
    | spl6_10 ),
    inference(subsumption_resolution,[],[f162,f45])).

fof(f162,plain,
    ( v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_xboole_0(sK0)
    | spl6_10 ),
    inference(subsumption_resolution,[],[f161,f49])).

fof(f161,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_xboole_0(sK0)
    | spl6_10 ),
    inference(subsumption_resolution,[],[f160,f48])).

fof(f160,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_xboole_0(sK0)
    | spl6_10 ),
    inference(subsumption_resolution,[],[f159,f50])).

fof(f159,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_xboole_0(sK0)
    | spl6_10 ),
    inference(resolution,[],[f149,f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f149,plain,
    ( ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | spl6_10 ),
    inference(avatar_component_clause,[],[f147])).

fof(f92,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f38,f89,f85,f81])).

fof(f38,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:23:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (2036)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.48  % (2034)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.49  % (2037)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (2042)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.50  % (2045)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  % (2044)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (2047)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (2039)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.50  % (2033)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (2032)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (2048)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.51  % (2038)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  % (2041)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.51  % (2040)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.51  % (2046)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.51  % (2050)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.52  % (2052)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.52  % (2051)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.52  % (2052)Refutation not found, incomplete strategy% (2052)------------------------------
% 0.22/0.52  % (2052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (2052)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (2052)Memory used [KB]: 10618
% 0.22/0.52  % (2052)Time elapsed: 0.104 s
% 0.22/0.52  % (2052)------------------------------
% 0.22/0.52  % (2052)------------------------------
% 0.22/0.52  % (2043)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.52  % (2035)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (2049)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.53  % (2033)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f531,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f92,f172,f205,f272,f298,f302,f312,f401,f445,f451,f485,f520])).
% 0.22/0.53  fof(f520,plain,(
% 0.22/0.53    spl6_1 | ~spl6_3 | ~spl6_10 | ~spl6_11 | ~spl6_20 | ~spl6_28),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f519])).
% 0.22/0.53  fof(f519,plain,(
% 0.22/0.53    $false | (spl6_1 | ~spl6_3 | ~spl6_10 | ~spl6_11 | ~spl6_20 | ~spl6_28)),
% 0.22/0.53    inference(subsumption_resolution,[],[f518,f453])).
% 0.22/0.53  fof(f453,plain,(
% 0.22/0.53    k1_xboole_0 = k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) | (~spl6_3 | ~spl6_28)),
% 0.22/0.53    inference(backward_demodulation,[],[f428,f442])).
% 0.22/0.53  fof(f442,plain,(
% 0.22/0.53    k1_xboole_0 = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | ~spl6_28),
% 0.22/0.53    inference(avatar_component_clause,[],[f440])).
% 0.22/0.53  fof(f440,plain,(
% 0.22/0.53    spl6_28 <=> k1_xboole_0 = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.22/0.54  fof(f428,plain,(
% 0.22/0.54    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | ~spl6_3),
% 0.22/0.54    inference(backward_demodulation,[],[f321,f424])).
% 0.22/0.54  fof(f424,plain,(
% 0.22/0.54    k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | ~spl6_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f423,f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    v1_funct_1(sK4)),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.54    inference(flattening,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,negated_conjecture,(
% 0.22/0.54    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 0.22/0.54    inference(negated_conjecture,[],[f16])).
% 0.22/0.54  fof(f16,conjecture,(
% 0.22/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tmap_1)).
% 0.22/0.54  fof(f423,plain,(
% 0.22/0.54    k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(sK4) | ~spl6_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f419,f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f419,plain,(
% 0.22/0.54    k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK4) | ~spl6_3),
% 0.22/0.54    inference(superposition,[],[f321,f71])).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.54    inference(flattening,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.22/0.54  fof(f321,plain,(
% 0.22/0.54    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | ~spl6_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f320,f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    v1_funct_1(sK5)),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f320,plain,(
% 0.22/0.54    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(sK5) | ~spl6_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f315,f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f315,plain,(
% 0.22/0.54    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(sK5) | ~spl6_3),
% 0.22/0.54    inference(superposition,[],[f90,f71])).
% 0.22/0.54  fof(f90,plain,(
% 0.22/0.54    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~spl6_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f89])).
% 0.22/0.54  fof(f89,plain,(
% 0.22/0.54    spl6_3 <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.54  fof(f518,plain,(
% 0.22/0.54    k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) | (spl6_1 | ~spl6_3 | ~spl6_10 | ~spl6_11 | ~spl6_20 | ~spl6_28)),
% 0.22/0.54    inference(subsumption_resolution,[],[f517,f152])).
% 0.22/0.54  fof(f152,plain,(
% 0.22/0.54    m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | ~spl6_11),
% 0.22/0.54    inference(avatar_component_clause,[],[f151])).
% 0.22/0.54  fof(f151,plain,(
% 0.22/0.54    spl6_11 <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.22/0.54  fof(f517,plain,(
% 0.22/0.54    ~m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) | (spl6_1 | ~spl6_3 | ~spl6_10 | ~spl6_20 | ~spl6_28)),
% 0.22/0.54    inference(subsumption_resolution,[],[f516,f241])).
% 0.22/0.54  fof(f241,plain,(
% 0.22/0.54    v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~spl6_20),
% 0.22/0.54    inference(avatar_component_clause,[],[f240])).
% 0.22/0.54  fof(f240,plain,(
% 0.22/0.54    spl6_20 <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.22/0.54  fof(f516,plain,(
% 0.22/0.54    ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) | (spl6_1 | ~spl6_3 | ~spl6_10 | ~spl6_28)),
% 0.22/0.54    inference(subsumption_resolution,[],[f515,f148])).
% 0.22/0.54  fof(f148,plain,(
% 0.22/0.54    v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~spl6_10),
% 0.22/0.54    inference(avatar_component_clause,[],[f147])).
% 0.22/0.54  fof(f147,plain,(
% 0.22/0.54    spl6_10 <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.54  fof(f515,plain,(
% 0.22/0.54    ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) | (spl6_1 | ~spl6_3 | ~spl6_28)),
% 0.22/0.54    inference(subsumption_resolution,[],[f514,f44])).
% 0.22/0.54  fof(f514,plain,(
% 0.22/0.54    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) | (spl6_1 | ~spl6_3 | ~spl6_28)),
% 0.22/0.54    inference(subsumption_resolution,[],[f513,f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    v1_funct_2(sK4,sK2,sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f513,plain,(
% 0.22/0.54    ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) | (spl6_1 | ~spl6_3 | ~spl6_28)),
% 0.22/0.54    inference(subsumption_resolution,[],[f511,f42])).
% 0.22/0.54  fof(f511,plain,(
% 0.22/0.54    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) | (spl6_1 | ~spl6_3 | ~spl6_28)),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f506])).
% 0.22/0.54  fof(f506,plain,(
% 0.22/0.54    sK5 != sK5 | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) | (spl6_1 | ~spl6_3 | ~spl6_28)),
% 0.22/0.54    inference(superposition,[],[f83,f456])).
% 0.22/0.54  fof(f456,plain,(
% 0.22/0.54    ( ! [X1] : (sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | k1_xboole_0 != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3))) ) | (~spl6_3 | ~spl6_28)),
% 0.22/0.54    inference(backward_demodulation,[],[f425,f442])).
% 0.22/0.54  fof(f425,plain,(
% 0.22/0.54    ( ! [X1] : (k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3)) ) | ~spl6_3),
% 0.22/0.54    inference(backward_demodulation,[],[f342,f424])).
% 0.22/0.54  fof(f342,plain,(
% 0.22/0.54    ( ! [X1] : (k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3)) ) | ~spl6_3),
% 0.22/0.54    inference(forward_demodulation,[],[f341,f321])).
% 0.22/0.54  fof(f341,plain,(
% 0.22/0.54    ( ! [X1] : (k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3)) ) | ~spl6_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f340,f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ~v1_xboole_0(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f340,plain,(
% 0.22/0.54    ( ! [X1] : (k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | v1_xboole_0(sK0) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3)) ) | ~spl6_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f339,f41])).
% 0.22/0.54  fof(f339,plain,(
% 0.22/0.54    ( ! [X1] : (k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3)) ) | ~spl6_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f338,f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    v1_funct_2(sK5,sK3,sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f338,plain,(
% 0.22/0.54    ( ! [X1] : (k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3)) ) | ~spl6_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f337,f39])).
% 0.22/0.54  fof(f337,plain,(
% 0.22/0.54    ( ! [X1] : (k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3)) ) | ~spl6_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f336,f46])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f336,plain,(
% 0.22/0.54    ( ! [X1] : (k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3)) ) | ~spl6_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f335,f45])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ~v1_xboole_0(sK3)),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f335,plain,(
% 0.22/0.54    ( ! [X1] : (k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3)) ) | ~spl6_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f334,f49])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f334,plain,(
% 0.22/0.54    ( ! [X1] : (k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3)) ) | ~spl6_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f333,f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ~v1_xboole_0(sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f333,plain,(
% 0.22/0.54    ( ! [X1] : (k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3)) ) | ~spl6_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f317,f50])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ~v1_xboole_0(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f317,plain,(
% 0.22/0.54    ( ! [X1] : (k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3)) ) | ~spl6_3),
% 0.22/0.54    inference(superposition,[],[f77,f90])).
% 0.22/0.54  fof(f77,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_xboole_0(X0) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5) )),
% 0.22/0.54    inference(equality_resolution,[],[f54])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.54    inference(flattening,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,axiom,(
% 0.22/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tmap_1)).
% 0.22/0.54  fof(f83,plain,(
% 0.22/0.54    sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | spl6_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f81])).
% 0.22/0.54  fof(f81,plain,(
% 0.22/0.54    spl6_1 <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.54  fof(f485,plain,(
% 0.22/0.54    spl6_2 | ~spl6_3 | ~spl6_10 | ~spl6_11 | ~spl6_20 | ~spl6_28),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f484])).
% 0.22/0.54  fof(f484,plain,(
% 0.22/0.54    $false | (spl6_2 | ~spl6_3 | ~spl6_10 | ~spl6_11 | ~spl6_20 | ~spl6_28)),
% 0.22/0.54    inference(subsumption_resolution,[],[f483,f453])).
% 0.22/0.54  fof(f483,plain,(
% 0.22/0.54    k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) | (spl6_2 | ~spl6_3 | ~spl6_10 | ~spl6_11 | ~spl6_20 | ~spl6_28)),
% 0.22/0.54    inference(subsumption_resolution,[],[f482,f152])).
% 0.22/0.54  fof(f482,plain,(
% 0.22/0.54    ~m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) | (spl6_2 | ~spl6_3 | ~spl6_10 | ~spl6_20 | ~spl6_28)),
% 0.22/0.54    inference(subsumption_resolution,[],[f481,f241])).
% 0.22/0.54  fof(f481,plain,(
% 0.22/0.54    ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) | (spl6_2 | ~spl6_3 | ~spl6_10 | ~spl6_28)),
% 0.22/0.54    inference(subsumption_resolution,[],[f480,f148])).
% 0.22/0.54  fof(f480,plain,(
% 0.22/0.54    ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) | (spl6_2 | ~spl6_3 | ~spl6_28)),
% 0.22/0.54    inference(subsumption_resolution,[],[f479,f44])).
% 0.22/0.54  fof(f479,plain,(
% 0.22/0.54    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) | (spl6_2 | ~spl6_3 | ~spl6_28)),
% 0.22/0.54    inference(subsumption_resolution,[],[f478,f43])).
% 0.22/0.54  fof(f478,plain,(
% 0.22/0.54    ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) | (spl6_2 | ~spl6_3 | ~spl6_28)),
% 0.22/0.54    inference(subsumption_resolution,[],[f476,f42])).
% 0.22/0.54  fof(f476,plain,(
% 0.22/0.54    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) | (spl6_2 | ~spl6_3 | ~spl6_28)),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f473])).
% 0.22/0.54  fof(f473,plain,(
% 0.22/0.54    sK4 != sK4 | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) | (spl6_2 | ~spl6_3 | ~spl6_28)),
% 0.22/0.54    inference(superposition,[],[f87,f455])).
% 0.22/0.54  fof(f455,plain,(
% 0.22/0.54    ( ! [X0] : (k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),sK2) = X0 | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK2,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | k1_xboole_0 != k2_partfun1(sK2,sK1,X0,k9_subset_1(sK0,sK2,sK3))) ) | (~spl6_3 | ~spl6_28)),
% 0.22/0.54    inference(backward_demodulation,[],[f426,f442])).
% 0.22/0.54  fof(f426,plain,(
% 0.22/0.54    ( ! [X0] : (k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X0,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK2,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),sK2) = X0) ) | ~spl6_3),
% 0.22/0.54    inference(backward_demodulation,[],[f332,f424])).
% 0.22/0.54  fof(f332,plain,(
% 0.22/0.54    ( ! [X0] : (k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X0,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK2,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),sK2) = X0) ) | ~spl6_3),
% 0.22/0.54    inference(forward_demodulation,[],[f331,f321])).
% 0.22/0.54  fof(f331,plain,(
% 0.22/0.54    ( ! [X0] : (k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X0,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK2,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),sK2) = X0) ) | ~spl6_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f330,f51])).
% 0.22/0.54  fof(f330,plain,(
% 0.22/0.54    ( ! [X0] : (k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X0,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK2,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | v1_xboole_0(sK0) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),sK2) = X0) ) | ~spl6_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f329,f41])).
% 0.22/0.54  fof(f329,plain,(
% 0.22/0.54    ( ! [X0] : (k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X0,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK2,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),sK2) = X0) ) | ~spl6_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f328,f40])).
% 0.22/0.54  fof(f328,plain,(
% 0.22/0.54    ( ! [X0] : (k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X0,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK2,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),sK2) = X0) ) | ~spl6_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f327,f39])).
% 0.22/0.54  fof(f327,plain,(
% 0.22/0.54    ( ! [X0] : (k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X0,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK2,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),sK2) = X0) ) | ~spl6_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f326,f46])).
% 0.22/0.54  fof(f326,plain,(
% 0.22/0.54    ( ! [X0] : (k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X0,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK2,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),sK2) = X0) ) | ~spl6_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f325,f45])).
% 0.22/0.54  fof(f325,plain,(
% 0.22/0.54    ( ! [X0] : (k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X0,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK2,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),sK2) = X0) ) | ~spl6_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f324,f49])).
% 0.22/0.54  fof(f324,plain,(
% 0.22/0.54    ( ! [X0] : (k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X0,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK2,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),sK2) = X0) ) | ~spl6_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f323,f48])).
% 0.22/0.54  fof(f323,plain,(
% 0.22/0.54    ( ! [X0] : (k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X0,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK2,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),sK2) = X0) ) | ~spl6_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f316,f50])).
% 0.22/0.54  fof(f316,plain,(
% 0.22/0.54    ( ! [X0] : (k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X0,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK2,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0,sK5),sK2) = X0) ) | ~spl6_3),
% 0.22/0.54    inference(superposition,[],[f78,f90])).
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_xboole_0(X0) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4) )),
% 0.22/0.54    inference(equality_resolution,[],[f53])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f87,plain,(
% 0.22/0.54    sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | spl6_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f85])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    spl6_2 <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.54  fof(f451,plain,(
% 0.22/0.54    ~spl6_25 | spl6_27),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f450])).
% 0.22/0.54  fof(f450,plain,(
% 0.22/0.54    $false | (~spl6_25 | spl6_27)),
% 0.22/0.54    inference(subsumption_resolution,[],[f449,f46])).
% 0.22/0.54  fof(f449,plain,(
% 0.22/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | (~spl6_25 | spl6_27)),
% 0.22/0.54    inference(subsumption_resolution,[],[f447,f387])).
% 0.22/0.54  fof(f387,plain,(
% 0.22/0.54    r1_xboole_0(k3_xboole_0(sK2,sK3),k1_relat_1(sK5)) | ~spl6_25),
% 0.22/0.54    inference(avatar_component_clause,[],[f386])).
% 0.22/0.54  fof(f386,plain,(
% 0.22/0.54    spl6_25 <=> r1_xboole_0(k3_xboole_0(sK2,sK3),k1_relat_1(sK5))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.22/0.54  fof(f447,plain,(
% 0.22/0.54    ~r1_xboole_0(k3_xboole_0(sK2,sK3),k1_relat_1(sK5)) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | spl6_27),
% 0.22/0.54    inference(superposition,[],[f438,f68])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.22/0.54  fof(f438,plain,(
% 0.22/0.54    ~r1_xboole_0(k9_subset_1(sK0,sK2,sK3),k1_relat_1(sK5)) | spl6_27),
% 0.22/0.54    inference(avatar_component_clause,[],[f436])).
% 0.22/0.54  fof(f436,plain,(
% 0.22/0.54    spl6_27 <=> r1_xboole_0(k9_subset_1(sK0,sK2,sK3),k1_relat_1(sK5))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.22/0.54  fof(f445,plain,(
% 0.22/0.54    ~spl6_27 | spl6_28 | ~spl6_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f444,f89,f440,f436])).
% 0.22/0.54  fof(f444,plain,(
% 0.22/0.54    k1_xboole_0 = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | ~r1_xboole_0(k9_subset_1(sK0,sK2,sK3),k1_relat_1(sK5)) | ~spl6_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f431,f126])).
% 0.22/0.54  fof(f126,plain,(
% 0.22/0.54    v1_relat_1(sK5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f113,f59])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.54  fof(f113,plain,(
% 0.22/0.54    ~v1_relat_1(k2_zfmisc_1(sK3,sK1)) | v1_relat_1(sK5)),
% 0.22/0.54    inference(resolution,[],[f41,f57])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.54  fof(f431,plain,(
% 0.22/0.54    k1_xboole_0 = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | ~r1_xboole_0(k9_subset_1(sK0,sK2,sK3),k1_relat_1(sK5)) | ~v1_relat_1(sK5) | ~spl6_3),
% 0.22/0.54    inference(superposition,[],[f56,f424])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).
% 0.22/0.54  fof(f401,plain,(
% 0.22/0.54    ~spl6_23 | spl6_25),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f400])).
% 0.22/0.54  fof(f400,plain,(
% 0.22/0.54    $false | (~spl6_23 | spl6_25)),
% 0.22/0.54    inference(subsumption_resolution,[],[f399,f95])).
% 0.22/0.54  fof(f95,plain,(
% 0.22/0.54    r1_xboole_0(sK2,sK3)),
% 0.22/0.54    inference(subsumption_resolution,[],[f94,f48])).
% 0.22/0.54  fof(f94,plain,(
% 0.22/0.54    r1_xboole_0(sK2,sK3) | v1_xboole_0(sK2)),
% 0.22/0.54    inference(subsumption_resolution,[],[f93,f45])).
% 0.22/0.54  fof(f93,plain,(
% 0.22/0.54    v1_xboole_0(sK3) | r1_xboole_0(sK2,sK3) | v1_xboole_0(sK2)),
% 0.22/0.54    inference(resolution,[],[f47,f63])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_subset_1(X0,X1) | v1_xboole_0(X1) | r1_xboole_0(X0,X1) | v1_xboole_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.22/0.54    inference(flattening,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    r1_subset_1(sK2,sK3)),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f399,plain,(
% 0.22/0.54    ~r1_xboole_0(sK2,sK3) | (~spl6_23 | spl6_25)),
% 0.22/0.54    inference(subsumption_resolution,[],[f397,f292])).
% 0.22/0.54  fof(f292,plain,(
% 0.22/0.54    r1_xboole_0(k1_xboole_0,k1_relat_1(sK5)) | ~spl6_23),
% 0.22/0.54    inference(avatar_component_clause,[],[f291])).
% 0.22/0.54  fof(f291,plain,(
% 0.22/0.54    spl6_23 <=> r1_xboole_0(k1_xboole_0,k1_relat_1(sK5))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.22/0.54  fof(f397,plain,(
% 0.22/0.54    ~r1_xboole_0(k1_xboole_0,k1_relat_1(sK5)) | ~r1_xboole_0(sK2,sK3) | spl6_25),
% 0.22/0.54    inference(superposition,[],[f388,f67])).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.54  fof(f388,plain,(
% 0.22/0.54    ~r1_xboole_0(k3_xboole_0(sK2,sK3),k1_relat_1(sK5)) | spl6_25),
% 0.22/0.54    inference(avatar_component_clause,[],[f386])).
% 0.22/0.54  fof(f312,plain,(
% 0.22/0.54    spl6_24),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f311])).
% 0.22/0.54  fof(f311,plain,(
% 0.22/0.54    $false | spl6_24),
% 0.22/0.54    inference(subsumption_resolution,[],[f309,f52])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.54  fof(f309,plain,(
% 0.22/0.54    ~r1_xboole_0(k1_relat_1(sK4),k1_xboole_0) | spl6_24),
% 0.22/0.54    inference(resolution,[],[f308,f61])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.22/0.54  fof(f308,plain,(
% 0.22/0.54    ~r1_xboole_0(k1_xboole_0,k1_relat_1(sK4)) | spl6_24),
% 0.22/0.54    inference(subsumption_resolution,[],[f307,f144])).
% 0.22/0.54  fof(f144,plain,(
% 0.22/0.54    v1_relat_1(sK4)),
% 0.22/0.54    inference(subsumption_resolution,[],[f131,f59])).
% 0.22/0.54  fof(f131,plain,(
% 0.22/0.54    ~v1_relat_1(k2_zfmisc_1(sK2,sK1)) | v1_relat_1(sK4)),
% 0.22/0.54    inference(resolution,[],[f44,f57])).
% 0.22/0.54  fof(f307,plain,(
% 0.22/0.54    ~r1_xboole_0(k1_xboole_0,k1_relat_1(sK4)) | ~v1_relat_1(sK4) | spl6_24),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f306])).
% 0.22/0.54  fof(f306,plain,(
% 0.22/0.54    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k1_xboole_0,k1_relat_1(sK4)) | ~v1_relat_1(sK4) | spl6_24),
% 0.22/0.54    inference(superposition,[],[f297,f56])).
% 0.22/0.54  fof(f297,plain,(
% 0.22/0.54    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | spl6_24),
% 0.22/0.54    inference(avatar_component_clause,[],[f295])).
% 0.22/0.54  fof(f295,plain,(
% 0.22/0.54    spl6_24 <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.22/0.54  fof(f302,plain,(
% 0.22/0.54    spl6_23),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f301])).
% 0.22/0.54  fof(f301,plain,(
% 0.22/0.54    $false | spl6_23),
% 0.22/0.54    inference(subsumption_resolution,[],[f299,f52])).
% 0.22/0.54  fof(f299,plain,(
% 0.22/0.54    ~r1_xboole_0(k1_relat_1(sK5),k1_xboole_0) | spl6_23),
% 0.22/0.54    inference(resolution,[],[f293,f61])).
% 0.22/0.54  fof(f293,plain,(
% 0.22/0.54    ~r1_xboole_0(k1_xboole_0,k1_relat_1(sK5)) | spl6_23),
% 0.22/0.54    inference(avatar_component_clause,[],[f291])).
% 0.22/0.54  fof(f298,plain,(
% 0.22/0.54    ~spl6_23 | ~spl6_24 | spl6_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f289,f89,f295,f291])).
% 0.22/0.54  fof(f289,plain,(
% 0.22/0.54    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | ~r1_xboole_0(k1_xboole_0,k1_relat_1(sK5)) | spl6_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f288,f126])).
% 0.22/0.54  fof(f288,plain,(
% 0.22/0.54    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | ~r1_xboole_0(k1_xboole_0,k1_relat_1(sK5)) | ~v1_relat_1(sK5) | spl6_3),
% 0.22/0.54    inference(superposition,[],[f287,f56])).
% 0.22/0.54  fof(f287,plain,(
% 0.22/0.54    k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) | spl6_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f286,f42])).
% 0.22/0.54  fof(f286,plain,(
% 0.22/0.54    k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) | ~v1_funct_1(sK4) | spl6_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f285,f44])).
% 0.22/0.54  fof(f285,plain,(
% 0.22/0.54    k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK4) | spl6_3),
% 0.22/0.54    inference(superposition,[],[f284,f71])).
% 0.22/0.54  fof(f284,plain,(
% 0.22/0.54    k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | spl6_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f283,f39])).
% 0.22/0.54  fof(f283,plain,(
% 0.22/0.54    k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | ~v1_funct_1(sK5) | spl6_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f282,f41])).
% 0.22/0.54  fof(f282,plain,(
% 0.22/0.54    k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(sK5) | spl6_3),
% 0.22/0.54    inference(superposition,[],[f275,f71])).
% 0.22/0.54  fof(f275,plain,(
% 0.22/0.54    k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) | spl6_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f273,f95])).
% 0.22/0.54  fof(f273,plain,(
% 0.22/0.54    k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) | ~r1_xboole_0(sK2,sK3) | spl6_3),
% 0.22/0.54    inference(superposition,[],[f256,f67])).
% 0.22/0.54  fof(f256,plain,(
% 0.22/0.54    k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) | spl6_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f254,f46])).
% 0.22/0.54  fof(f254,plain,(
% 0.22/0.54    k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | spl6_3),
% 0.22/0.54    inference(superposition,[],[f91,f68])).
% 0.22/0.54  fof(f91,plain,(
% 0.22/0.54    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | spl6_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f89])).
% 0.22/0.54  fof(f272,plain,(
% 0.22/0.54    spl6_20),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f271])).
% 0.22/0.54  fof(f271,plain,(
% 0.22/0.54    $false | spl6_20),
% 0.22/0.54    inference(subsumption_resolution,[],[f270,f51])).
% 0.22/0.54  fof(f270,plain,(
% 0.22/0.54    v1_xboole_0(sK0) | spl6_20),
% 0.22/0.54    inference(subsumption_resolution,[],[f269,f41])).
% 0.22/0.54  fof(f269,plain,(
% 0.22/0.54    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | spl6_20),
% 0.22/0.54    inference(subsumption_resolution,[],[f268,f40])).
% 0.22/0.54  fof(f268,plain,(
% 0.22/0.54    ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | spl6_20),
% 0.22/0.54    inference(subsumption_resolution,[],[f267,f39])).
% 0.22/0.54  fof(f267,plain,(
% 0.22/0.54    ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | spl6_20),
% 0.22/0.54    inference(subsumption_resolution,[],[f266,f44])).
% 0.22/0.54  fof(f266,plain,(
% 0.22/0.54    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | spl6_20),
% 0.22/0.54    inference(subsumption_resolution,[],[f265,f43])).
% 0.22/0.54  fof(f265,plain,(
% 0.22/0.54    ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | spl6_20),
% 0.22/0.54    inference(subsumption_resolution,[],[f264,f42])).
% 0.22/0.54  fof(f264,plain,(
% 0.22/0.54    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | spl6_20),
% 0.22/0.54    inference(subsumption_resolution,[],[f263,f46])).
% 0.22/0.54  fof(f263,plain,(
% 0.22/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | spl6_20),
% 0.22/0.54    inference(subsumption_resolution,[],[f262,f45])).
% 0.22/0.54  fof(f262,plain,(
% 0.22/0.54    v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | spl6_20),
% 0.22/0.54    inference(subsumption_resolution,[],[f261,f49])).
% 0.22/0.54  fof(f261,plain,(
% 0.22/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | spl6_20),
% 0.22/0.54    inference(subsumption_resolution,[],[f260,f48])).
% 0.22/0.54  fof(f260,plain,(
% 0.22/0.54    v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | spl6_20),
% 0.22/0.54    inference(subsumption_resolution,[],[f259,f50])).
% 0.22/0.54  fof(f259,plain,(
% 0.22/0.54    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | spl6_20),
% 0.22/0.54    inference(resolution,[],[f242,f73])).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_xboole_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.22/0.54    inference(flattening,[],[f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tmap_1)).
% 0.22/0.54  fof(f242,plain,(
% 0.22/0.54    ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | spl6_20),
% 0.22/0.54    inference(avatar_component_clause,[],[f240])).
% 0.22/0.54  fof(f205,plain,(
% 0.22/0.54    spl6_11),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f204])).
% 0.22/0.54  fof(f204,plain,(
% 0.22/0.54    $false | spl6_11),
% 0.22/0.54    inference(subsumption_resolution,[],[f203,f51])).
% 0.22/0.54  fof(f203,plain,(
% 0.22/0.54    v1_xboole_0(sK0) | spl6_11),
% 0.22/0.54    inference(subsumption_resolution,[],[f202,f41])).
% 0.22/0.54  fof(f202,plain,(
% 0.22/0.54    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | spl6_11),
% 0.22/0.54    inference(subsumption_resolution,[],[f201,f40])).
% 0.22/0.54  fof(f201,plain,(
% 0.22/0.54    ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | spl6_11),
% 0.22/0.54    inference(subsumption_resolution,[],[f200,f39])).
% 0.22/0.54  fof(f200,plain,(
% 0.22/0.54    ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | spl6_11),
% 0.22/0.54    inference(subsumption_resolution,[],[f199,f44])).
% 0.22/0.54  fof(f199,plain,(
% 0.22/0.54    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | spl6_11),
% 0.22/0.54    inference(subsumption_resolution,[],[f198,f43])).
% 0.22/0.54  fof(f198,plain,(
% 0.22/0.54    ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | spl6_11),
% 0.22/0.54    inference(subsumption_resolution,[],[f197,f42])).
% 0.22/0.54  fof(f197,plain,(
% 0.22/0.54    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | spl6_11),
% 0.22/0.54    inference(subsumption_resolution,[],[f196,f46])).
% 0.22/0.54  fof(f196,plain,(
% 0.22/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | spl6_11),
% 0.22/0.54    inference(subsumption_resolution,[],[f195,f45])).
% 0.22/0.54  fof(f195,plain,(
% 0.22/0.54    v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | spl6_11),
% 0.22/0.54    inference(subsumption_resolution,[],[f194,f49])).
% 0.22/0.54  fof(f194,plain,(
% 0.22/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | spl6_11),
% 0.22/0.54    inference(subsumption_resolution,[],[f193,f48])).
% 0.22/0.54  fof(f193,plain,(
% 0.22/0.54    v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | spl6_11),
% 0.22/0.54    inference(subsumption_resolution,[],[f192,f50])).
% 0.22/0.54  fof(f192,plain,(
% 0.22/0.54    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | spl6_11),
% 0.22/0.54    inference(resolution,[],[f153,f74])).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_xboole_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f37])).
% 0.22/0.54  fof(f153,plain,(
% 0.22/0.54    ~m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | spl6_11),
% 0.22/0.54    inference(avatar_component_clause,[],[f151])).
% 0.22/0.54  fof(f172,plain,(
% 0.22/0.54    spl6_10),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f171])).
% 0.22/0.54  fof(f171,plain,(
% 0.22/0.54    $false | spl6_10),
% 0.22/0.54    inference(subsumption_resolution,[],[f170,f51])).
% 0.22/0.54  fof(f170,plain,(
% 0.22/0.54    v1_xboole_0(sK0) | spl6_10),
% 0.22/0.54    inference(subsumption_resolution,[],[f169,f41])).
% 0.22/0.54  fof(f169,plain,(
% 0.22/0.54    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | spl6_10),
% 0.22/0.54    inference(subsumption_resolution,[],[f168,f40])).
% 0.22/0.54  fof(f168,plain,(
% 0.22/0.54    ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | spl6_10),
% 0.22/0.54    inference(subsumption_resolution,[],[f167,f39])).
% 0.22/0.54  fof(f167,plain,(
% 0.22/0.54    ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | spl6_10),
% 0.22/0.54    inference(subsumption_resolution,[],[f166,f44])).
% 0.22/0.54  fof(f166,plain,(
% 0.22/0.54    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | spl6_10),
% 0.22/0.54    inference(subsumption_resolution,[],[f165,f43])).
% 0.22/0.54  fof(f165,plain,(
% 0.22/0.54    ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | spl6_10),
% 0.22/0.54    inference(subsumption_resolution,[],[f164,f42])).
% 0.22/0.54  fof(f164,plain,(
% 0.22/0.54    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | spl6_10),
% 0.22/0.54    inference(subsumption_resolution,[],[f163,f46])).
% 0.22/0.54  fof(f163,plain,(
% 0.22/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | spl6_10),
% 0.22/0.54    inference(subsumption_resolution,[],[f162,f45])).
% 0.22/0.54  fof(f162,plain,(
% 0.22/0.54    v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | spl6_10),
% 0.22/0.54    inference(subsumption_resolution,[],[f161,f49])).
% 0.22/0.54  fof(f161,plain,(
% 0.22/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | spl6_10),
% 0.22/0.54    inference(subsumption_resolution,[],[f160,f48])).
% 0.22/0.54  fof(f160,plain,(
% 0.22/0.54    v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | spl6_10),
% 0.22/0.54    inference(subsumption_resolution,[],[f159,f50])).
% 0.22/0.54  fof(f159,plain,(
% 0.22/0.54    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK0) | spl6_10),
% 0.22/0.54    inference(resolution,[],[f149,f72])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_xboole_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f37])).
% 0.22/0.54  fof(f149,plain,(
% 0.22/0.54    ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | spl6_10),
% 0.22/0.54    inference(avatar_component_clause,[],[f147])).
% 0.22/0.54  fof(f92,plain,(
% 0.22/0.54    ~spl6_1 | ~spl6_2 | ~spl6_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f38,f89,f85,f81])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (2033)------------------------------
% 0.22/0.54  % (2033)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (2033)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (2033)Memory used [KB]: 10874
% 0.22/0.54  % (2033)Time elapsed: 0.099 s
% 0.22/0.54  % (2033)------------------------------
% 0.22/0.54  % (2033)------------------------------
% 0.22/0.54  % (2031)Success in time 0.18 s
%------------------------------------------------------------------------------
