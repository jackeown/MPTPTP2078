%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 155 expanded)
%              Number of leaves         :   28 (  66 expanded)
%              Depth                    :   11
%              Number of atoms          :  288 ( 500 expanded)
%              Number of equality atoms :   65 (  98 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f205,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f71,f88,f101,f122,f138,f144,f153,f159,f193,f204])).

fof(f204,plain,
    ( spl4_12
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f203,f190,f118,f85,f156])).

fof(f156,plain,
    ( spl4_12
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f85,plain,
    ( spl4_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f118,plain,
    ( spl4_8
  <=> sK2 = k7_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f190,plain,
    ( spl4_15
  <=> r1_xboole_0(k1_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f203,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f202,f42])).

fof(f42,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f202,plain,
    ( k1_relat_1(sK2) = k5_xboole_0(k1_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f201,f120])).

fof(f120,plain,
    ( sK2 = k7_relat_1(sK2,sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f118])).

fof(f201,plain,
    ( k1_relat_1(sK2) = k5_xboole_0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ spl4_5
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f195,f125])).

fof(f125,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK2,X0)) = k3_xboole_0(k1_relat_1(sK2),X0)
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f87,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f87,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f195,plain,
    ( k1_relat_1(sK2) = k5_xboole_0(k1_relat_1(sK2),k3_xboole_0(k1_relat_1(sK2),sK1))
    | ~ spl4_15 ),
    inference(resolution,[],[f192,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f54,f47])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f192,plain,
    ( r1_xboole_0(k1_relat_1(sK2),sK1)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f190])).

fof(f193,plain,
    ( spl4_15
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f188,f149,f190])).

fof(f149,plain,
    ( spl4_11
  <=> k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f188,plain,
    ( r1_xboole_0(k1_relat_1(sK2),sK1)
    | ~ spl4_11 ),
    inference(duplicate_literal_removal,[],[f187])).

fof(f187,plain,
    ( r1_xboole_0(k1_relat_1(sK2),sK1)
    | r1_xboole_0(k1_relat_1(sK2),sK1)
    | ~ spl4_11 ),
    inference(resolution,[],[f169,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f169,plain,
    ( ! [X16] :
        ( ~ r2_hidden(sK3(X16,sK1),k1_relat_1(sK2))
        | r1_xboole_0(X16,sK1) )
    | ~ spl4_11 ),
    inference(resolution,[],[f91,f160])).

fof(f160,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,sK1)
        | ~ r2_hidden(X3,k1_relat_1(sK2)) )
    | ~ spl4_11 ),
    inference(backward_demodulation,[],[f41,f151])).

fof(f151,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f149])).

fof(f41,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK1)
      | ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))
        | ~ m1_subset_1(X3,sK1) )
    & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f31,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
                    | ~ m1_subset_1(X3,X1) )
                & k1_xboole_0 != k2_relset_1(X1,X0,X2)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k1_relset_1(X1,sK0,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k2_relset_1(X1,sK0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ! [X3] :
                ( ~ r2_hidden(X3,k1_relset_1(X1,sK0,X2))
                | ~ m1_subset_1(X3,X1) )
            & k1_xboole_0 != k2_relset_1(X1,sK0,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,X2))
              | ~ m1_subset_1(X3,sK1) )
          & k1_xboole_0 != k2_relset_1(sK1,sK0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,X2))
            | ~ m1_subset_1(X3,sK1) )
        & k1_xboole_0 != k2_relset_1(sK1,sK0,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) )
   => ( ! [X3] :
          ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))
          | ~ m1_subset_1(X3,sK1) )
      & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k2_relset_1(X1,X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

% (6573)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k2_relset_1(X1,X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                    & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                  & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relset_1)).

fof(f91,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f49,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f159,plain,
    ( ~ spl4_12
    | ~ spl4_5
    | spl4_10 ),
    inference(avatar_split_clause,[],[f154,f141,f85,f156])).

fof(f141,plain,
    ( spl4_10
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f154,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | ~ spl4_5
    | spl4_10 ),
    inference(unit_resulting_resolution,[],[f87,f143,f43])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f143,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f141])).

fof(f153,plain,
    ( spl4_11
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f146,f68,f149])).

fof(f68,plain,
    ( spl4_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f146,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f57,f70])).

fof(f70,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f144,plain,
    ( ~ spl4_10
    | spl4_1
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f139,f134,f63,f141])).

fof(f63,plain,
    ( spl4_1
  <=> k1_xboole_0 = k2_relset_1(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f134,plain,
    ( spl4_9
  <=> k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f139,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | spl4_1
    | ~ spl4_9 ),
    inference(superposition,[],[f65,f136])).

fof(f136,plain,
    ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f134])).

fof(f65,plain,
    ( k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f138,plain,
    ( spl4_9
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f131,f68,f134])).

fof(f131,plain,
    ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f56,f70])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f122,plain,
    ( ~ spl4_5
    | spl4_8
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f116,f97,f118,f85])).

fof(f97,plain,
    ( spl4_6
  <=> v4_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f116,plain,
    ( sK2 = k7_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl4_6 ),
    inference(resolution,[],[f53,f99])).

fof(f99,plain,
    ( v4_relat_1(sK2,sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f101,plain,
    ( spl4_6
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f95,f68,f97])).

fof(f95,plain,
    ( v4_relat_1(sK2,sK1)
    | ~ spl4_2 ),
    inference(resolution,[],[f58,f70])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f88,plain,
    ( spl4_5
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f82,f68,f85])).

fof(f82,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f46,f70,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f46,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f71,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f39,f68])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f66,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f40,f63])).

fof(f40,plain,(
    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:43:48 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.44  % (6576)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.45  % (6576)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f205,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(avatar_sat_refutation,[],[f66,f71,f88,f101,f122,f138,f144,f153,f159,f193,f204])).
% 0.20/0.45  fof(f204,plain,(
% 0.20/0.45    spl4_12 | ~spl4_5 | ~spl4_8 | ~spl4_15),
% 0.20/0.45    inference(avatar_split_clause,[],[f203,f190,f118,f85,f156])).
% 0.20/0.45  fof(f156,plain,(
% 0.20/0.45    spl4_12 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.45  fof(f85,plain,(
% 0.20/0.45    spl4_5 <=> v1_relat_1(sK2)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.45  fof(f118,plain,(
% 0.20/0.45    spl4_8 <=> sK2 = k7_relat_1(sK2,sK1)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.45  fof(f190,plain,(
% 0.20/0.45    spl4_15 <=> r1_xboole_0(k1_relat_1(sK2),sK1)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.45  fof(f203,plain,(
% 0.20/0.45    k1_xboole_0 = k1_relat_1(sK2) | (~spl4_5 | ~spl4_8 | ~spl4_15)),
% 0.20/0.45    inference(forward_demodulation,[],[f202,f42])).
% 0.20/0.45  fof(f42,plain,(
% 0.20/0.45    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 0.20/0.45    inference(cnf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.20/0.45  fof(f202,plain,(
% 0.20/0.45    k1_relat_1(sK2) = k5_xboole_0(k1_relat_1(sK2),k1_relat_1(sK2)) | (~spl4_5 | ~spl4_8 | ~spl4_15)),
% 0.20/0.45    inference(forward_demodulation,[],[f201,f120])).
% 0.20/0.45  fof(f120,plain,(
% 0.20/0.45    sK2 = k7_relat_1(sK2,sK1) | ~spl4_8),
% 0.20/0.45    inference(avatar_component_clause,[],[f118])).
% 0.20/0.45  fof(f201,plain,(
% 0.20/0.45    k1_relat_1(sK2) = k5_xboole_0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1))) | (~spl4_5 | ~spl4_15)),
% 0.20/0.45    inference(forward_demodulation,[],[f195,f125])).
% 0.20/0.45  fof(f125,plain,(
% 0.20/0.45    ( ! [X0] : (k1_relat_1(k7_relat_1(sK2,X0)) = k3_xboole_0(k1_relat_1(sK2),X0)) ) | ~spl4_5),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f87,f51])).
% 0.20/0.45  fof(f51,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f22])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f10])).
% 0.20/0.45  fof(f10,axiom,(
% 0.20/0.45    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.20/0.45  fof(f87,plain,(
% 0.20/0.45    v1_relat_1(sK2) | ~spl4_5),
% 0.20/0.45    inference(avatar_component_clause,[],[f85])).
% 0.20/0.45  fof(f195,plain,(
% 0.20/0.45    k1_relat_1(sK2) = k5_xboole_0(k1_relat_1(sK2),k3_xboole_0(k1_relat_1(sK2),sK1)) | ~spl4_15),
% 0.20/0.45    inference(resolution,[],[f192,f61])).
% 0.20/0.45  fof(f61,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.20/0.45    inference(definition_unfolding,[],[f54,f47])).
% 0.20/0.45  fof(f47,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.45  fof(f54,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f36])).
% 0.20/0.45  fof(f36,plain,(
% 0.20/0.45    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.45    inference(nnf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.20/0.45  fof(f192,plain,(
% 0.20/0.45    r1_xboole_0(k1_relat_1(sK2),sK1) | ~spl4_15),
% 0.20/0.45    inference(avatar_component_clause,[],[f190])).
% 0.20/0.45  fof(f193,plain,(
% 0.20/0.45    spl4_15 | ~spl4_11),
% 0.20/0.45    inference(avatar_split_clause,[],[f188,f149,f190])).
% 0.20/0.45  fof(f149,plain,(
% 0.20/0.45    spl4_11 <=> k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.45  fof(f188,plain,(
% 0.20/0.45    r1_xboole_0(k1_relat_1(sK2),sK1) | ~spl4_11),
% 0.20/0.45    inference(duplicate_literal_removal,[],[f187])).
% 0.20/0.45  fof(f187,plain,(
% 0.20/0.45    r1_xboole_0(k1_relat_1(sK2),sK1) | r1_xboole_0(k1_relat_1(sK2),sK1) | ~spl4_11),
% 0.20/0.45    inference(resolution,[],[f169,f48])).
% 0.20/0.45  fof(f48,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f35])).
% 0.20/0.45  fof(f35,plain,(
% 0.20/0.45    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f34])).
% 0.20/0.45  fof(f34,plain,(
% 0.20/0.45    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.45    inference(ennf_transformation,[],[f16])).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.45    inference(rectify,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.45  fof(f169,plain,(
% 0.20/0.45    ( ! [X16] : (~r2_hidden(sK3(X16,sK1),k1_relat_1(sK2)) | r1_xboole_0(X16,sK1)) ) | ~spl4_11),
% 0.20/0.45    inference(resolution,[],[f91,f160])).
% 0.20/0.45  fof(f160,plain,(
% 0.20/0.45    ( ! [X3] : (~m1_subset_1(X3,sK1) | ~r2_hidden(X3,k1_relat_1(sK2))) ) | ~spl4_11),
% 0.20/0.45    inference(backward_demodulation,[],[f41,f151])).
% 0.20/0.45  fof(f151,plain,(
% 0.20/0.45    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) | ~spl4_11),
% 0.20/0.45    inference(avatar_component_clause,[],[f149])).
% 0.20/0.45  fof(f41,plain,(
% 0.20/0.45    ( ! [X3] : (~m1_subset_1(X3,sK1) | ~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f32])).
% 0.20/0.45  fof(f32,plain,(
% 0.20/0.45    ((! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f31,f30,f29])).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,sK0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,sK0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f30,plain,(
% 0.20/0.45    ? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,sK0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,sK0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))) & ~v1_xboole_0(X1)) => (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,X2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k2_relset_1(sK1,sK0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))) & ~v1_xboole_0(sK1))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f31,plain,(
% 0.20/0.45    ? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,X2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k2_relset_1(sK1,sK0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))) => (! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.45    inference(flattening,[],[f17])).
% 0.20/0.45  % (6573)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f15])).
% 0.20/0.45  fof(f15,negated_conjecture,(
% 0.20/0.45    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 0.20/0.45    inference(negated_conjecture,[],[f14])).
% 0.20/0.45  fof(f14,conjecture,(
% 0.20/0.45    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relset_1)).
% 0.20/0.45  fof(f91,plain,(
% 0.20/0.45    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.20/0.45    inference(resolution,[],[f49,f52])).
% 0.20/0.45  fof(f52,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f23])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f5])).
% 0.20/0.45  fof(f5,axiom,(
% 0.20/0.45    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.20/0.45  fof(f49,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f35])).
% 0.20/0.45  fof(f159,plain,(
% 0.20/0.45    ~spl4_12 | ~spl4_5 | spl4_10),
% 0.20/0.45    inference(avatar_split_clause,[],[f154,f141,f85,f156])).
% 0.20/0.45  fof(f141,plain,(
% 0.20/0.45    spl4_10 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.45  fof(f154,plain,(
% 0.20/0.45    k1_xboole_0 != k1_relat_1(sK2) | (~spl4_5 | spl4_10)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f87,f143,f43])).
% 0.20/0.45  fof(f43,plain,(
% 0.20/0.45    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f33])).
% 0.20/0.45  fof(f33,plain,(
% 0.20/0.45    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.45    inference(nnf_transformation,[],[f19])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f9])).
% 0.20/0.45  fof(f9,axiom,(
% 0.20/0.45    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 0.20/0.45  fof(f143,plain,(
% 0.20/0.45    k1_xboole_0 != k2_relat_1(sK2) | spl4_10),
% 0.20/0.45    inference(avatar_component_clause,[],[f141])).
% 0.20/0.45  fof(f153,plain,(
% 0.20/0.45    spl4_11 | ~spl4_2),
% 0.20/0.45    inference(avatar_split_clause,[],[f146,f68,f149])).
% 0.20/0.45  fof(f68,plain,(
% 0.20/0.45    spl4_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.45  fof(f146,plain,(
% 0.20/0.45    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) | ~spl4_2),
% 0.20/0.45    inference(resolution,[],[f57,f70])).
% 0.20/0.45  fof(f70,plain,(
% 0.20/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_2),
% 0.20/0.45    inference(avatar_component_clause,[],[f68])).
% 0.20/0.45  fof(f57,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f27])).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.45    inference(ennf_transformation,[],[f12])).
% 0.20/0.45  fof(f12,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.45  fof(f144,plain,(
% 0.20/0.45    ~spl4_10 | spl4_1 | ~spl4_9),
% 0.20/0.45    inference(avatar_split_clause,[],[f139,f134,f63,f141])).
% 0.20/0.45  fof(f63,plain,(
% 0.20/0.45    spl4_1 <=> k1_xboole_0 = k2_relset_1(sK1,sK0,sK2)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.45  fof(f134,plain,(
% 0.20/0.45    spl4_9 <=> k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.45  fof(f139,plain,(
% 0.20/0.45    k1_xboole_0 != k2_relat_1(sK2) | (spl4_1 | ~spl4_9)),
% 0.20/0.45    inference(superposition,[],[f65,f136])).
% 0.20/0.45  fof(f136,plain,(
% 0.20/0.45    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) | ~spl4_9),
% 0.20/0.45    inference(avatar_component_clause,[],[f134])).
% 0.20/0.45  fof(f65,plain,(
% 0.20/0.45    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) | spl4_1),
% 0.20/0.45    inference(avatar_component_clause,[],[f63])).
% 0.20/0.45  fof(f138,plain,(
% 0.20/0.45    spl4_9 | ~spl4_2),
% 0.20/0.45    inference(avatar_split_clause,[],[f131,f68,f134])).
% 0.20/0.45  fof(f131,plain,(
% 0.20/0.45    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) | ~spl4_2),
% 0.20/0.45    inference(resolution,[],[f56,f70])).
% 0.20/0.45  fof(f56,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f26])).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.45    inference(ennf_transformation,[],[f13])).
% 0.20/0.45  fof(f13,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.45  fof(f122,plain,(
% 0.20/0.45    ~spl4_5 | spl4_8 | ~spl4_6),
% 0.20/0.45    inference(avatar_split_clause,[],[f116,f97,f118,f85])).
% 0.20/0.45  fof(f97,plain,(
% 0.20/0.45    spl4_6 <=> v4_relat_1(sK2,sK1)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.45  fof(f116,plain,(
% 0.20/0.45    sK2 = k7_relat_1(sK2,sK1) | ~v1_relat_1(sK2) | ~spl4_6),
% 0.20/0.45    inference(resolution,[],[f53,f99])).
% 0.20/0.45  fof(f99,plain,(
% 0.20/0.45    v4_relat_1(sK2,sK1) | ~spl4_6),
% 0.20/0.45    inference(avatar_component_clause,[],[f97])).
% 0.20/0.45  fof(f53,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f25])).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.45    inference(flattening,[],[f24])).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.45    inference(ennf_transformation,[],[f8])).
% 0.20/0.45  fof(f8,axiom,(
% 0.20/0.45    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.20/0.45  fof(f101,plain,(
% 0.20/0.45    spl4_6 | ~spl4_2),
% 0.20/0.45    inference(avatar_split_clause,[],[f95,f68,f97])).
% 0.20/0.45  fof(f95,plain,(
% 0.20/0.45    v4_relat_1(sK2,sK1) | ~spl4_2),
% 0.20/0.45    inference(resolution,[],[f58,f70])).
% 0.20/0.45  fof(f58,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f28])).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.45    inference(ennf_transformation,[],[f11])).
% 0.20/0.45  fof(f11,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.45  fof(f88,plain,(
% 0.20/0.45    spl4_5 | ~spl4_2),
% 0.20/0.45    inference(avatar_split_clause,[],[f82,f68,f85])).
% 0.20/0.45  fof(f82,plain,(
% 0.20/0.45    v1_relat_1(sK2) | ~spl4_2),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f46,f70,f45])).
% 0.20/0.45  fof(f45,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f20])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,axiom,(
% 0.20/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.45  fof(f46,plain,(
% 0.20/0.45    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f7])).
% 0.20/0.45  fof(f7,axiom,(
% 0.20/0.45    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.45  fof(f71,plain,(
% 0.20/0.45    spl4_2),
% 0.20/0.45    inference(avatar_split_clause,[],[f39,f68])).
% 0.20/0.45  fof(f39,plain,(
% 0.20/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.45    inference(cnf_transformation,[],[f32])).
% 0.20/0.45  fof(f66,plain,(
% 0.20/0.45    ~spl4_1),
% 0.20/0.45    inference(avatar_split_clause,[],[f40,f63])).
% 0.20/0.45  fof(f40,plain,(
% 0.20/0.45    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)),
% 0.20/0.45    inference(cnf_transformation,[],[f32])).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (6576)------------------------------
% 0.20/0.45  % (6576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (6576)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (6576)Memory used [KB]: 6268
% 0.20/0.45  % (6576)Time elapsed: 0.038 s
% 0.20/0.45  % (6576)------------------------------
% 0.20/0.45  % (6576)------------------------------
% 0.20/0.45  % (6567)Success in time 0.092 s
%------------------------------------------------------------------------------
