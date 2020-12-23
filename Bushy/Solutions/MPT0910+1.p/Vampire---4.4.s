%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t70_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:12 EDT 2019

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 109 expanded)
%              Number of leaves         :   16 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :  197 ( 439 expanded)
%              Number of equality atoms :   68 ( 198 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f156,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f63,f70,f77,f84,f91,f108,f130,f141,f152,f155])).

fof(f155,plain,
    ( ~ spl6_6
    | spl6_19 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | ~ spl6_6
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f153,f76])).

fof(f76,plain,
    ( m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl6_6
  <=> m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f153,plain,
    ( ~ m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))
    | ~ spl6_19 ),
    inference(resolution,[],[f129,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t70_mcart_1.p',dt_k6_mcart_1)).

fof(f129,plain,
    ( ~ m1_subset_1(k6_mcart_1(sK0,sK1,sK2,sK4),sK1)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl6_19
  <=> ~ m1_subset_1(k6_mcart_1(sK0,sK1,sK2,sK4),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f152,plain,
    ( ~ spl6_6
    | spl6_17 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | ~ spl6_6
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f150,f76])).

fof(f150,plain,
    ( ~ m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))
    | ~ spl6_17 ),
    inference(resolution,[],[f123,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t70_mcart_1.p',dt_k7_mcart_1)).

fof(f123,plain,
    ( ~ m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK4),sK2)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl6_17
  <=> ~ m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f141,plain,
    ( ~ spl6_6
    | spl6_15 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | ~ spl6_6
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f139,f76])).

fof(f139,plain,
    ( ~ m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))
    | ~ spl6_15 ),
    inference(resolution,[],[f117,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t70_mcart_1.p',dt_k5_mcart_1)).

fof(f117,plain,
    ( ~ m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl6_15
  <=> ~ m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f130,plain,
    ( ~ spl6_15
    | ~ spl6_17
    | ~ spl6_19
    | spl6_9
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f111,f106,f82,f128,f122,f116])).

fof(f82,plain,
    ( spl6_9
  <=> k6_mcart_1(sK0,sK1,sK2,sK4) != sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f106,plain,
    ( spl6_12
  <=> k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK4),k6_mcart_1(sK0,sK1,sK2,sK4),k7_mcart_1(sK0,sK1,sK2,sK4)) = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f111,plain,
    ( ~ m1_subset_1(k6_mcart_1(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK4),sK2)
    | ~ m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0)
    | ~ spl6_9
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f110,f83])).

fof(f83,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK4) != sK3
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f82])).

fof(f110,plain,
    ( ~ m1_subset_1(k6_mcart_1(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK4),sK2)
    | ~ m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0)
    | k6_mcart_1(sK0,sK1,sK2,sK4) = sK3
    | ~ spl6_12 ),
    inference(trivial_inequality_removal,[],[f109])).

fof(f109,plain,
    ( sK4 != sK4
    | ~ m1_subset_1(k6_mcart_1(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK4),sK2)
    | ~ m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0)
    | k6_mcart_1(sK0,sK1,sK2,sK4) = sK3
    | ~ spl6_12 ),
    inference(superposition,[],[f33,f107])).

fof(f107,plain,
    ( k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK4),k6_mcart_1(sK0,sK1,sK2,sK4),k7_mcart_1(sK0,sK1,sK2,sK4)) = sK4
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f106])).

fof(f33,plain,(
    ! [X6,X7,X5] :
      ( k3_mcart_1(X5,X6,X7) != sK4
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X5,sK0)
      | sK3 = X6 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k6_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X6
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k6_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X6
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X6 ) ) ) )
         => ( k6_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X6 ) ) ) )
       => ( k6_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t70_mcart_1.p',t70_mcart_1)).

fof(f108,plain,
    ( spl6_12
    | spl6_1
    | spl6_3
    | spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f101,f75,f68,f61,f54,f106])).

fof(f54,plain,
    ( spl6_1
  <=> k1_xboole_0 != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f61,plain,
    ( spl6_3
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f68,plain,
    ( spl6_5
  <=> k1_xboole_0 != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f101,plain,
    ( k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK4),k6_mcart_1(sK0,sK1,sK2,sK4),k7_mcart_1(sK0,sK1,sK2,sK4)) = sK4
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f100,f55])).

fof(f55,plain,
    ( k1_xboole_0 != sK0
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f100,plain,
    ( k1_xboole_0 = sK0
    | k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK4),k6_mcart_1(sK0,sK1,sK2,sK4),k7_mcart_1(sK0,sK1,sK2,sK4)) = sK4
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f99,f69])).

fof(f69,plain,
    ( k1_xboole_0 != sK2
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f99,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK4),k6_mcart_1(sK0,sK1,sK2,sK4),k7_mcart_1(sK0,sK1,sK2,sK4)) = sK4
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f97,f62])).

fof(f62,plain,
    ( k1_xboole_0 != sK1
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f97,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK4),k6_mcart_1(sK0,sK1,sK2,sK4),k7_mcart_1(sK0,sK1,sK2,sK4)) = sK4
    | ~ spl6_6 ),
    inference(resolution,[],[f40,f76])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t70_mcart_1.p',t48_mcart_1)).

fof(f91,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f42,f89])).

fof(f89,plain,
    ( spl6_10
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f42,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t70_mcart_1.p',d2_xboole_0)).

fof(f84,plain,(
    ~ spl6_9 ),
    inference(avatar_split_clause,[],[f38,f82])).

fof(f38,plain,(
    k6_mcart_1(sK0,sK1,sK2,sK4) != sK3 ),
    inference(cnf_transformation,[],[f23])).

fof(f77,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f34,f75])).

fof(f34,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f70,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f37,f68])).

fof(f37,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f23])).

fof(f63,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f36,f61])).

fof(f36,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f35,f54])).

fof(f35,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
