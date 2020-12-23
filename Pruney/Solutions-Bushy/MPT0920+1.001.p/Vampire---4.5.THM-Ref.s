%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0920+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:53 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 129 expanded)
%              Number of leaves         :   17 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :  255 ( 599 expanded)
%              Number of equality atoms :   84 ( 262 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f99,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f36,f41,f46,f51,f56,f70,f75,f80,f85,f90,f98])).

fof(f98,plain,
    ( spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11 ),
    inference(avatar_contradiction_clause,[],[f97])).

fof(f97,plain,
    ( $false
    | spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f96,f55])).

fof(f55,plain,
    ( sK4 != k9_mcart_1(sK0,sK1,sK2,sK3,sK5)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl6_6
  <=> sK4 = k9_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f96,plain,
    ( sK4 = k9_mcart_1(sK0,sK1,sK2,sK3,sK5)
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f95,f74])).

fof(f74,plain,
    ( m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl6_8
  <=> m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f95,plain,
    ( ~ m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0)
    | sK4 = k9_mcart_1(sK0,sK1,sK2,sK3,sK5)
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f94,f79])).

fof(f79,plain,
    ( m1_subset_1(k11_mcart_1(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl6_9
  <=> m1_subset_1(k11_mcart_1(sK0,sK1,sK2,sK3,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f94,plain,
    ( ~ m1_subset_1(k11_mcart_1(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0)
    | sK4 = k9_mcart_1(sK0,sK1,sK2,sK3,sK5)
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f93,f84])).

fof(f84,plain,
    ( m1_subset_1(k10_mcart_1(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl6_10
  <=> m1_subset_1(k10_mcart_1(sK0,sK1,sK2,sK3,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f93,plain,
    ( ~ m1_subset_1(k10_mcart_1(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(k11_mcart_1(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0)
    | sK4 = k9_mcart_1(sK0,sK1,sK2,sK3,sK5)
    | ~ spl6_7
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f92,f69])).

fof(f69,plain,
    ( m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl6_7
  <=> m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f92,plain,
    ( ~ m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(k10_mcart_1(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(k11_mcart_1(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0)
    | sK4 = k9_mcart_1(sK0,sK1,sK2,sK3,sK5)
    | ~ spl6_11 ),
    inference(trivial_inequality_removal,[],[f91])).

fof(f91,plain,
    ( sK5 != sK5
    | ~ m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(k10_mcart_1(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(k11_mcart_1(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0)
    | sK4 = k9_mcart_1(sK0,sK1,sK2,sK3,sK5)
    | ~ spl6_11 ),
    inference(superposition,[],[f15,f89])).

fof(f89,plain,
    ( sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl6_11
  <=> sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f15,plain,(
    ! [X6,X8,X7,X9] :
      ( k4_mcart_1(X6,X7,X8,X9) != sK5
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X9,sK3)
      | ~ m1_subset_1(X6,sK0)
      | sK4 = X7 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k9_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X7
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k9_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X7
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
       => ( ! [X6] :
              ( m1_subset_1(X6,X0)
             => ! [X7] :
                  ( m1_subset_1(X7,X1)
                 => ! [X8] :
                      ( m1_subset_1(X8,X2)
                     => ! [X9] :
                          ( m1_subset_1(X9,X3)
                         => ( k4_mcart_1(X6,X7,X8,X9) = X5
                           => X4 = X7 ) ) ) ) )
         => ( k9_mcart_1(X0,X1,X2,X3,X5) = X4
            | k1_xboole_0 = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
     => ( ! [X6] :
            ( m1_subset_1(X6,X0)
           => ! [X7] :
                ( m1_subset_1(X7,X1)
               => ! [X8] :
                    ( m1_subset_1(X8,X2)
                   => ! [X9] :
                        ( m1_subset_1(X9,X3)
                       => ( k4_mcart_1(X6,X7,X8,X9) = X5
                         => X4 = X7 ) ) ) ) )
       => ( k9_mcart_1(X0,X1,X2,X3,X5) = X4
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_mcart_1)).

fof(f90,plain,
    ( spl6_11
    | spl6_1
    | spl6_2
    | spl6_3
    | spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f65,f48,f43,f38,f33,f28,f87])).

fof(f28,plain,
    ( spl6_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f33,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f38,plain,
    ( spl6_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f43,plain,
    ( spl6_4
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f48,plain,
    ( spl6_5
  <=> m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f65,plain,
    ( sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5))
    | spl6_1
    | spl6_2
    | spl6_3
    | spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f64,f30])).

fof(f30,plain,
    ( k1_xboole_0 != sK0
    | spl6_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f64,plain,
    ( k1_xboole_0 = sK0
    | sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5))
    | spl6_2
    | spl6_3
    | spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f63,f45])).

fof(f45,plain,
    ( k1_xboole_0 != sK3
    | spl6_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f63,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5))
    | spl6_2
    | spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f62,f40])).

fof(f40,plain,
    ( k1_xboole_0 != sK2
    | spl6_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f62,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5))
    | spl6_2
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f61,f35])).

fof(f35,plain,
    ( k1_xboole_0 != sK1
    | spl6_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f61,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5))
    | ~ spl6_5 ),
    inference(resolution,[],[f50,f22])).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_mcart_1)).

fof(f50,plain,
    ( m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f48])).

fof(f85,plain,
    ( spl6_10
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f60,f48,f82])).

fof(f60,plain,
    ( m1_subset_1(k10_mcart_1(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ spl6_5 ),
    inference(resolution,[],[f50,f23])).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_mcart_1)).

fof(f80,plain,
    ( spl6_9
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f59,f48,f77])).

fof(f59,plain,
    ( m1_subset_1(k11_mcart_1(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ spl6_5 ),
    inference(resolution,[],[f50,f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_mcart_1)).

fof(f75,plain,
    ( spl6_8
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f58,f48,f72])).

fof(f58,plain,
    ( m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0)
    | ~ spl6_5 ),
    inference(resolution,[],[f50,f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_mcart_1)).

fof(f70,plain,
    ( spl6_7
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f57,f48,f67])).

fof(f57,plain,
    ( m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ spl6_5 ),
    inference(resolution,[],[f50,f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_mcart_1)).

fof(f56,plain,(
    ~ spl6_6 ),
    inference(avatar_split_clause,[],[f21,f53])).

fof(f21,plain,(
    sK4 != k9_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f9])).

fof(f51,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f16,f48])).

fof(f16,plain,(
    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f46,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f20,f43])).

fof(f20,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f9])).

fof(f41,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f19,f38])).

fof(f19,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f9])).

fof(f36,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f18,f33])).

fof(f18,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f31,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f17,f28])).

fof(f17,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f9])).

%------------------------------------------------------------------------------
