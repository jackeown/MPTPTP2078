%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 277 expanded)
%              Number of leaves         :   27 ( 112 expanded)
%              Depth                    :   12
%              Number of atoms          :  515 ( 895 expanded)
%              Number of equality atoms :   18 (  49 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f309,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f69,f82,f86,f91,f98,f113,f126,f134,f154,f179,f209,f269,f280,f290,f308])).

fof(f308,plain,
    ( ~ spl9_1
    | ~ spl9_3
    | spl9_7
    | ~ spl9_29
    | ~ spl9_30
    | ~ spl9_31 ),
    inference(avatar_contradiction_clause,[],[f307])).

fof(f307,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_3
    | spl9_7
    | ~ spl9_29
    | ~ spl9_30
    | ~ spl9_31 ),
    inference(subsumption_resolution,[],[f306,f81])).

fof(f81,plain,
    ( v1_relat_1(sK3)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl9_3
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f306,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl9_1
    | spl9_7
    | ~ spl9_29
    | ~ spl9_30
    | ~ spl9_31 ),
    inference(subsumption_resolution,[],[f305,f286])).

fof(f286,plain,
    ( sK4 != k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4))
    | spl9_7
    | ~ spl9_29
    | ~ spl9_30 ),
    inference(subsumption_resolution,[],[f283,f282])).

fof(f282,plain,
    ( r2_hidden(sK6(sK2,sK0,sK3,sK4),sK0)
    | spl9_7
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f281,f97])).

fof(f97,plain,
    ( ~ v1_xboole_0(sK0)
    | spl9_7 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl9_7
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f281,plain,
    ( v1_xboole_0(sK0)
    | r2_hidden(sK6(sK2,sK0,sK3,sK4),sK0)
    | ~ spl9_29 ),
    inference(resolution,[],[f268,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f268,plain,
    ( m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0)
    | ~ spl9_29 ),
    inference(avatar_component_clause,[],[f267])).

fof(f267,plain,
    ( spl9_29
  <=> m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).

fof(f283,plain,
    ( ~ r2_hidden(sK6(sK2,sK0,sK3,sK4),sK0)
    | sK4 != k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4))
    | ~ spl9_30 ),
    inference(resolution,[],[f279,f34])).

fof(f34,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X5,sK0)
      | sK4 != k1_funct_1(sK3,X5) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

% (14983)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ~ ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

fof(f279,plain,
    ( r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2)
    | ~ spl9_30 ),
    inference(avatar_component_clause,[],[f278])).

fof(f278,plain,
    ( spl9_30
  <=> r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f305,plain,
    ( sK4 = k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4))
    | ~ v1_relat_1(sK3)
    | ~ spl9_1
    | ~ spl9_31 ),
    inference(subsumption_resolution,[],[f298,f64])).

fof(f64,plain,
    ( v1_funct_1(sK3)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl9_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f298,plain,
    ( ~ v1_funct_1(sK3)
    | sK4 = k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4))
    | ~ v1_relat_1(sK3)
    | ~ spl9_31 ),
    inference(resolution,[],[f289,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f289,plain,
    ( r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3)
    | ~ spl9_31 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl9_31
  <=> r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).

fof(f290,plain,
    ( spl9_31
    | ~ spl9_2
    | ~ spl9_5
    | spl9_7
    | spl9_8
    | spl9_12
    | ~ spl9_21 ),
    inference(avatar_split_clause,[],[f274,f207,f132,f111,f96,f89,f67,f288])).

fof(f67,plain,
    ( spl9_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f89,plain,
    ( spl9_5
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f111,plain,
    ( spl9_8
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f132,plain,
    ( spl9_12
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f207,plain,
    ( spl9_21
  <=> m1_subset_1(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f274,plain,
    ( r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3)
    | ~ spl9_2
    | ~ spl9_5
    | spl9_7
    | spl9_8
    | spl9_12
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f273,f208])).

fof(f208,plain,
    ( m1_subset_1(sK4,sK1)
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f207])).

fof(f273,plain,
    ( ~ m1_subset_1(sK4,sK1)
    | r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3)
    | ~ spl9_2
    | ~ spl9_5
    | spl9_7
    | spl9_8
    | spl9_12 ),
    inference(subsumption_resolution,[],[f270,f133])).

fof(f133,plain,
    ( ~ v1_xboole_0(sK2)
    | spl9_12 ),
    inference(avatar_component_clause,[],[f132])).

fof(f270,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(sK4,sK1)
    | r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3)
    | ~ spl9_2
    | ~ spl9_5
    | spl9_7
    | spl9_8 ),
    inference(resolution,[],[f174,f90])).

fof(f90,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f174,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X4,k9_relat_1(sK3,X3))
        | v1_xboole_0(X3)
        | ~ m1_subset_1(X4,sK1)
        | r2_hidden(k4_tarski(sK6(X3,sK0,sK3,X4),X4),sK3) )
    | ~ spl9_2
    | spl9_7
    | spl9_8 ),
    inference(subsumption_resolution,[],[f173,f112])).

fof(f112,plain,
    ( ~ v1_xboole_0(sK1)
    | spl9_8 ),
    inference(avatar_component_clause,[],[f111])).

fof(f173,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X4,k9_relat_1(sK3,X3))
        | v1_xboole_0(X3)
        | ~ m1_subset_1(X4,sK1)
        | r2_hidden(k4_tarski(sK6(X3,sK0,sK3,X4),X4),sK3)
        | v1_xboole_0(sK1) )
    | ~ spl9_2
    | spl9_7 ),
    inference(subsumption_resolution,[],[f172,f68])).

fof(f68,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f172,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X4,k9_relat_1(sK3,X3))
        | v1_xboole_0(X3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X4,sK1)
        | r2_hidden(k4_tarski(sK6(X3,sK0,sK3,X4),X4),sK3)
        | v1_xboole_0(sK1) )
    | ~ spl9_2
    | spl9_7 ),
    inference(subsumption_resolution,[],[f167,f97])).

fof(f167,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X4,k9_relat_1(sK3,X3))
        | v1_xboole_0(X3)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X4,sK1)
        | r2_hidden(k4_tarski(sK6(X3,sK0,sK3,X4),X4),sK3)
        | v1_xboole_0(sK1) )
    | ~ spl9_2 ),
    inference(superposition,[],[f48,f75])).

fof(f75,plain,
    ( ! [X4] : k7_relset_1(sK0,sK1,sK3,X4) = k9_relat_1(sK3,X4)
    | ~ spl9_2 ),
    inference(resolution,[],[f68,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X4,X0)
      | r2_hidden(k4_tarski(sK6(X1,X2,X3,X4),X4),X3)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relset_1)).

fof(f280,plain,
    ( spl9_30
    | ~ spl9_2
    | ~ spl9_5
    | spl9_7
    | spl9_8
    | spl9_12
    | ~ spl9_21 ),
    inference(avatar_split_clause,[],[f263,f207,f132,f111,f96,f89,f67,f278])).

fof(f263,plain,
    ( r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2)
    | ~ spl9_2
    | ~ spl9_5
    | spl9_7
    | spl9_8
    | spl9_12
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f262,f208])).

fof(f262,plain,
    ( ~ m1_subset_1(sK4,sK1)
    | r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2)
    | ~ spl9_2
    | ~ spl9_5
    | spl9_7
    | spl9_8
    | spl9_12 ),
    inference(subsumption_resolution,[],[f259,f133])).

fof(f259,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(sK4,sK1)
    | r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2)
    | ~ spl9_2
    | ~ spl9_5
    | spl9_7
    | spl9_8 ),
    inference(resolution,[],[f177,f90])).

fof(f177,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X6,k9_relat_1(sK3,X5))
        | v1_xboole_0(X5)
        | ~ m1_subset_1(X6,sK1)
        | r2_hidden(sK6(X5,sK0,sK3,X6),X5) )
    | ~ spl9_2
    | spl9_7
    | spl9_8 ),
    inference(subsumption_resolution,[],[f176,f112])).

fof(f176,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X6,k9_relat_1(sK3,X5))
        | v1_xboole_0(X5)
        | ~ m1_subset_1(X6,sK1)
        | r2_hidden(sK6(X5,sK0,sK3,X6),X5)
        | v1_xboole_0(sK1) )
    | ~ spl9_2
    | spl9_7 ),
    inference(subsumption_resolution,[],[f175,f68])).

fof(f175,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X6,k9_relat_1(sK3,X5))
        | v1_xboole_0(X5)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X6,sK1)
        | r2_hidden(sK6(X5,sK0,sK3,X6),X5)
        | v1_xboole_0(sK1) )
    | ~ spl9_2
    | spl9_7 ),
    inference(subsumption_resolution,[],[f168,f97])).

fof(f168,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X6,k9_relat_1(sK3,X5))
        | v1_xboole_0(X5)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X6,sK1)
        | r2_hidden(sK6(X5,sK0,sK3,X6),X5)
        | v1_xboole_0(sK1) )
    | ~ spl9_2 ),
    inference(superposition,[],[f49,f75])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X4,X0)
      | r2_hidden(sK6(X1,X2,X3,X4),X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f269,plain,
    ( spl9_29
    | ~ spl9_2
    | ~ spl9_5
    | spl9_7
    | spl9_8
    | spl9_12
    | ~ spl9_21 ),
    inference(avatar_split_clause,[],[f256,f207,f132,f111,f96,f89,f67,f267])).

fof(f256,plain,
    ( m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0)
    | ~ spl9_2
    | ~ spl9_5
    | spl9_7
    | spl9_8
    | spl9_12
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f255,f208])).

fof(f255,plain,
    ( ~ m1_subset_1(sK4,sK1)
    | m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0)
    | ~ spl9_2
    | ~ spl9_5
    | spl9_7
    | spl9_8
    | spl9_12 ),
    inference(subsumption_resolution,[],[f252,f133])).

fof(f252,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(sK4,sK1)
    | m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0)
    | ~ spl9_2
    | ~ spl9_5
    | spl9_7
    | spl9_8 ),
    inference(resolution,[],[f171,f90])).

fof(f171,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X2,k9_relat_1(sK3,X1))
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X2,sK1)
        | m1_subset_1(sK6(X1,sK0,sK3,X2),sK0) )
    | ~ spl9_2
    | spl9_7
    | spl9_8 ),
    inference(subsumption_resolution,[],[f170,f112])).

fof(f170,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X2,k9_relat_1(sK3,X1))
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X2,sK1)
        | m1_subset_1(sK6(X1,sK0,sK3,X2),sK0)
        | v1_xboole_0(sK1) )
    | ~ spl9_2
    | spl9_7 ),
    inference(subsumption_resolution,[],[f169,f68])).

fof(f169,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X2,k9_relat_1(sK3,X1))
        | v1_xboole_0(X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X2,sK1)
        | m1_subset_1(sK6(X1,sK0,sK3,X2),sK0)
        | v1_xboole_0(sK1) )
    | ~ spl9_2
    | spl9_7 ),
    inference(subsumption_resolution,[],[f166,f97])).

fof(f166,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X2,k9_relat_1(sK3,X1))
        | v1_xboole_0(X1)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X2,sK1)
        | m1_subset_1(sK6(X1,sK0,sK3,X2),sK0)
        | v1_xboole_0(sK1) )
    | ~ spl9_2 ),
    inference(superposition,[],[f47,f75])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X4,X0)
      | m1_subset_1(sK6(X1,X2,X3,X4),X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f209,plain,
    ( spl9_21
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f203,f89,f67,f207])).

fof(f203,plain,
    ( m1_subset_1(sK4,sK1)
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(resolution,[],[f165,f105])).

fof(f105,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(X0))
        | m1_subset_1(sK4,X0) )
    | ~ spl9_5 ),
    inference(resolution,[],[f90,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f165,plain,
    ( ! [X0] : m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(sK1))
    | ~ spl9_2 ),
    inference(superposition,[],[f74,f75])).

fof(f74,plain,
    ( ! [X3] : m1_subset_1(k7_relset_1(sK0,sK1,sK3,X3),k1_zfmisc_1(sK1))
    | ~ spl9_2 ),
    inference(resolution,[],[f68,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f179,plain,
    ( ~ spl9_6
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f158,f152,f93])).

fof(f93,plain,
    ( spl9_6
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f152,plain,
    ( spl9_15
  <=> r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f158,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl9_15 ),
    inference(resolution,[],[f153,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f153,plain,
    ( r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3)
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f152])).

fof(f154,plain,
    ( spl9_15
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f107,f89,f80,f152])).

fof(f107,plain,
    ( r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3)
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f102,f81])).

fof(f102,plain,
    ( r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl9_5 ),
    inference(resolution,[],[f90,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f134,plain,
    ( ~ spl9_12
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f128,f124,f132])).

fof(f124,plain,
    ( spl9_11
  <=> r2_hidden(sK8(sK4,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f128,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl9_11 ),
    inference(resolution,[],[f125,f45])).

fof(f125,plain,
    ( r2_hidden(sK8(sK4,sK2,sK3),sK2)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f124])).

fof(f126,plain,
    ( spl9_11
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f108,f89,f80,f124])).

fof(f108,plain,
    ( r2_hidden(sK8(sK4,sK2,sK3),sK2)
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f103,f81])).

fof(f103,plain,
    ( r2_hidden(sK8(sK4,sK2,sK3),sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl9_5 ),
    inference(resolution,[],[f90,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK8(X0,X1,X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f113,plain,
    ( spl9_6
    | ~ spl9_8
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f72,f67,f111,f93])).

fof(f72,plain,
    ( ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK3)
    | ~ spl9_2 ),
    inference(resolution,[],[f68,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f98,plain,
    ( spl9_6
    | ~ spl9_7
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f71,f67,f96,f93])).

fof(f71,plain,
    ( ~ v1_xboole_0(sK0)
    | v1_xboole_0(sK3)
    | ~ spl9_2 ),
    inference(resolution,[],[f68,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f91,plain,
    ( spl9_5
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f87,f84,f67,f89])).

fof(f84,plain,
    ( spl9_4
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f87,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(forward_demodulation,[],[f85,f75])).

fof(f85,plain,
    ( r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f86,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f35,f84])).

fof(f35,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f82,plain,
    ( spl9_3
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f70,f67,f80])).

fof(f70,plain,
    ( v1_relat_1(sK3)
    | ~ spl9_2 ),
    inference(resolution,[],[f68,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f69,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f37,f67])).

fof(f37,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f65,plain,(
    spl9_1 ),
    inference(avatar_split_clause,[],[f36,f63])).

fof(f36,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 20:14:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.21/0.48  % (14971)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (14980)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (14972)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (14985)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (14977)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  % (14979)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  % (14966)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (14978)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (14968)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.52  % (14967)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (14982)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.52  % (14967)Refutation not found, incomplete strategy% (14967)------------------------------
% 0.21/0.52  % (14967)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (14967)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (14967)Memory used [KB]: 10618
% 0.21/0.52  % (14967)Time elapsed: 0.091 s
% 0.21/0.52  % (14967)------------------------------
% 0.21/0.52  % (14967)------------------------------
% 0.21/0.52  % (14969)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (14976)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.52  % (14970)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.53  % (14974)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.53  % (14973)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.53  % (14981)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.53  % (14975)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.53  % (14986)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.53  % (14966)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f309,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f65,f69,f82,f86,f91,f98,f113,f126,f134,f154,f179,f209,f269,f280,f290,f308])).
% 0.21/0.53  fof(f308,plain,(
% 0.21/0.53    ~spl9_1 | ~spl9_3 | spl9_7 | ~spl9_29 | ~spl9_30 | ~spl9_31),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f307])).
% 0.21/0.53  fof(f307,plain,(
% 0.21/0.53    $false | (~spl9_1 | ~spl9_3 | spl9_7 | ~spl9_29 | ~spl9_30 | ~spl9_31)),
% 0.21/0.53    inference(subsumption_resolution,[],[f306,f81])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    v1_relat_1(sK3) | ~spl9_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f80])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    spl9_3 <=> v1_relat_1(sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.21/0.53  fof(f306,plain,(
% 0.21/0.53    ~v1_relat_1(sK3) | (~spl9_1 | spl9_7 | ~spl9_29 | ~spl9_30 | ~spl9_31)),
% 0.21/0.53    inference(subsumption_resolution,[],[f305,f286])).
% 0.21/0.53  fof(f286,plain,(
% 0.21/0.53    sK4 != k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4)) | (spl9_7 | ~spl9_29 | ~spl9_30)),
% 0.21/0.53    inference(subsumption_resolution,[],[f283,f282])).
% 0.21/0.53  fof(f282,plain,(
% 0.21/0.53    r2_hidden(sK6(sK2,sK0,sK3,sK4),sK0) | (spl9_7 | ~spl9_29)),
% 0.21/0.53    inference(subsumption_resolution,[],[f281,f97])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    ~v1_xboole_0(sK0) | spl9_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f96])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    spl9_7 <=> v1_xboole_0(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.21/0.53  fof(f281,plain,(
% 0.21/0.53    v1_xboole_0(sK0) | r2_hidden(sK6(sK2,sK0,sK3,sK4),sK0) | ~spl9_29),
% 0.21/0.53    inference(resolution,[],[f268,f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.53    inference(flattening,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.53  fof(f268,plain,(
% 0.21/0.53    m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0) | ~spl9_29),
% 0.21/0.53    inference(avatar_component_clause,[],[f267])).
% 0.21/0.53  fof(f267,plain,(
% 0.21/0.53    spl9_29 <=> m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).
% 0.21/0.53  fof(f283,plain,(
% 0.21/0.53    ~r2_hidden(sK6(sK2,sK0,sK3,sK4),sK0) | sK4 != k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4)) | ~spl9_30),
% 0.21/0.53    inference(resolution,[],[f279,f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X5] : (~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0) | sK4 != k1_funct_1(sK3,X5)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 0.21/0.53    inference(flattening,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 0.21/0.53    inference(ennf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.53    inference(pure_predicate_removal,[],[f15])).
% 0.21/0.53  % (14983)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.53  fof(f15,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.53    inference(negated_conjecture,[],[f14])).
% 0.21/0.53  fof(f14,conjecture,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).
% 0.21/0.53  fof(f279,plain,(
% 0.21/0.53    r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2) | ~spl9_30),
% 0.21/0.53    inference(avatar_component_clause,[],[f278])).
% 0.21/0.53  fof(f278,plain,(
% 0.21/0.53    spl9_30 <=> r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).
% 0.21/0.53  fof(f305,plain,(
% 0.21/0.53    sK4 = k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4)) | ~v1_relat_1(sK3) | (~spl9_1 | ~spl9_31)),
% 0.21/0.53    inference(subsumption_resolution,[],[f298,f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    v1_funct_1(sK3) | ~spl9_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f63])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    spl9_1 <=> v1_funct_1(sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.53  fof(f298,plain,(
% 0.21/0.53    ~v1_funct_1(sK3) | sK4 = k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4)) | ~v1_relat_1(sK3) | ~spl9_31),
% 0.21/0.53    inference(resolution,[],[f289,f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.53    inference(flattening,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.53  fof(f289,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3) | ~spl9_31),
% 0.21/0.53    inference(avatar_component_clause,[],[f288])).
% 0.21/0.53  fof(f288,plain,(
% 0.21/0.53    spl9_31 <=> r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).
% 0.21/0.53  fof(f290,plain,(
% 0.21/0.53    spl9_31 | ~spl9_2 | ~spl9_5 | spl9_7 | spl9_8 | spl9_12 | ~spl9_21),
% 0.21/0.53    inference(avatar_split_clause,[],[f274,f207,f132,f111,f96,f89,f67,f288])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    spl9_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    spl9_5 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    spl9_8 <=> v1_xboole_0(sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    spl9_12 <=> v1_xboole_0(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 0.21/0.53  fof(f207,plain,(
% 0.21/0.53    spl9_21 <=> m1_subset_1(sK4,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 0.21/0.53  fof(f274,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3) | (~spl9_2 | ~spl9_5 | spl9_7 | spl9_8 | spl9_12 | ~spl9_21)),
% 0.21/0.53    inference(subsumption_resolution,[],[f273,f208])).
% 0.21/0.53  fof(f208,plain,(
% 0.21/0.53    m1_subset_1(sK4,sK1) | ~spl9_21),
% 0.21/0.53    inference(avatar_component_clause,[],[f207])).
% 0.21/0.53  fof(f273,plain,(
% 0.21/0.53    ~m1_subset_1(sK4,sK1) | r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3) | (~spl9_2 | ~spl9_5 | spl9_7 | spl9_8 | spl9_12)),
% 0.21/0.53    inference(subsumption_resolution,[],[f270,f133])).
% 0.21/0.53  fof(f133,plain,(
% 0.21/0.53    ~v1_xboole_0(sK2) | spl9_12),
% 0.21/0.53    inference(avatar_component_clause,[],[f132])).
% 0.21/0.53  fof(f270,plain,(
% 0.21/0.53    v1_xboole_0(sK2) | ~m1_subset_1(sK4,sK1) | r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3) | (~spl9_2 | ~spl9_5 | spl9_7 | spl9_8)),
% 0.21/0.53    inference(resolution,[],[f174,f90])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~spl9_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f89])).
% 0.21/0.53  fof(f174,plain,(
% 0.21/0.53    ( ! [X4,X3] : (~r2_hidden(X4,k9_relat_1(sK3,X3)) | v1_xboole_0(X3) | ~m1_subset_1(X4,sK1) | r2_hidden(k4_tarski(sK6(X3,sK0,sK3,X4),X4),sK3)) ) | (~spl9_2 | spl9_7 | spl9_8)),
% 0.21/0.53    inference(subsumption_resolution,[],[f173,f112])).
% 0.21/0.53  fof(f112,plain,(
% 0.21/0.53    ~v1_xboole_0(sK1) | spl9_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f111])).
% 0.21/0.53  fof(f173,plain,(
% 0.21/0.53    ( ! [X4,X3] : (~r2_hidden(X4,k9_relat_1(sK3,X3)) | v1_xboole_0(X3) | ~m1_subset_1(X4,sK1) | r2_hidden(k4_tarski(sK6(X3,sK0,sK3,X4),X4),sK3) | v1_xboole_0(sK1)) ) | (~spl9_2 | spl9_7)),
% 0.21/0.53    inference(subsumption_resolution,[],[f172,f68])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl9_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f67])).
% 0.21/0.53  fof(f172,plain,(
% 0.21/0.53    ( ! [X4,X3] : (~r2_hidden(X4,k9_relat_1(sK3,X3)) | v1_xboole_0(X3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X4,sK1) | r2_hidden(k4_tarski(sK6(X3,sK0,sK3,X4),X4),sK3) | v1_xboole_0(sK1)) ) | (~spl9_2 | spl9_7)),
% 0.21/0.53    inference(subsumption_resolution,[],[f167,f97])).
% 0.21/0.53  fof(f167,plain,(
% 0.21/0.53    ( ! [X4,X3] : (~r2_hidden(X4,k9_relat_1(sK3,X3)) | v1_xboole_0(X3) | v1_xboole_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X4,sK1) | r2_hidden(k4_tarski(sK6(X3,sK0,sK3,X4),X4),sK3) | v1_xboole_0(sK1)) ) | ~spl9_2),
% 0.21/0.53    inference(superposition,[],[f48,f75])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ( ! [X4] : (k7_relset_1(sK0,sK1,sK3,X4) = k9_relat_1(sK3,X4)) ) | ~spl9_2),
% 0.21/0.53    inference(resolution,[],[f68,f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X4,X0) | r2_hidden(k4_tarski(sK6(X1,X2,X3,X4),X4),X3) | v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relset_1)).
% 0.21/0.53  fof(f280,plain,(
% 0.21/0.53    spl9_30 | ~spl9_2 | ~spl9_5 | spl9_7 | spl9_8 | spl9_12 | ~spl9_21),
% 0.21/0.53    inference(avatar_split_clause,[],[f263,f207,f132,f111,f96,f89,f67,f278])).
% 0.21/0.53  fof(f263,plain,(
% 0.21/0.53    r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2) | (~spl9_2 | ~spl9_5 | spl9_7 | spl9_8 | spl9_12 | ~spl9_21)),
% 0.21/0.53    inference(subsumption_resolution,[],[f262,f208])).
% 0.21/0.53  fof(f262,plain,(
% 0.21/0.53    ~m1_subset_1(sK4,sK1) | r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2) | (~spl9_2 | ~spl9_5 | spl9_7 | spl9_8 | spl9_12)),
% 0.21/0.53    inference(subsumption_resolution,[],[f259,f133])).
% 0.21/0.53  fof(f259,plain,(
% 0.21/0.53    v1_xboole_0(sK2) | ~m1_subset_1(sK4,sK1) | r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2) | (~spl9_2 | ~spl9_5 | spl9_7 | spl9_8)),
% 0.21/0.53    inference(resolution,[],[f177,f90])).
% 0.21/0.53  fof(f177,plain,(
% 0.21/0.53    ( ! [X6,X5] : (~r2_hidden(X6,k9_relat_1(sK3,X5)) | v1_xboole_0(X5) | ~m1_subset_1(X6,sK1) | r2_hidden(sK6(X5,sK0,sK3,X6),X5)) ) | (~spl9_2 | spl9_7 | spl9_8)),
% 0.21/0.53    inference(subsumption_resolution,[],[f176,f112])).
% 0.21/0.53  fof(f176,plain,(
% 0.21/0.53    ( ! [X6,X5] : (~r2_hidden(X6,k9_relat_1(sK3,X5)) | v1_xboole_0(X5) | ~m1_subset_1(X6,sK1) | r2_hidden(sK6(X5,sK0,sK3,X6),X5) | v1_xboole_0(sK1)) ) | (~spl9_2 | spl9_7)),
% 0.21/0.53    inference(subsumption_resolution,[],[f175,f68])).
% 0.21/0.53  fof(f175,plain,(
% 0.21/0.53    ( ! [X6,X5] : (~r2_hidden(X6,k9_relat_1(sK3,X5)) | v1_xboole_0(X5) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X6,sK1) | r2_hidden(sK6(X5,sK0,sK3,X6),X5) | v1_xboole_0(sK1)) ) | (~spl9_2 | spl9_7)),
% 0.21/0.53    inference(subsumption_resolution,[],[f168,f97])).
% 0.21/0.53  fof(f168,plain,(
% 0.21/0.53    ( ! [X6,X5] : (~r2_hidden(X6,k9_relat_1(sK3,X5)) | v1_xboole_0(X5) | v1_xboole_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X6,sK1) | r2_hidden(sK6(X5,sK0,sK3,X6),X5) | v1_xboole_0(sK1)) ) | ~spl9_2),
% 0.21/0.53    inference(superposition,[],[f49,f75])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X4,X0) | r2_hidden(sK6(X1,X2,X3,X4),X1) | v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f269,plain,(
% 0.21/0.53    spl9_29 | ~spl9_2 | ~spl9_5 | spl9_7 | spl9_8 | spl9_12 | ~spl9_21),
% 0.21/0.53    inference(avatar_split_clause,[],[f256,f207,f132,f111,f96,f89,f67,f267])).
% 0.21/0.53  fof(f256,plain,(
% 0.21/0.53    m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0) | (~spl9_2 | ~spl9_5 | spl9_7 | spl9_8 | spl9_12 | ~spl9_21)),
% 0.21/0.53    inference(subsumption_resolution,[],[f255,f208])).
% 0.21/0.53  fof(f255,plain,(
% 0.21/0.53    ~m1_subset_1(sK4,sK1) | m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0) | (~spl9_2 | ~spl9_5 | spl9_7 | spl9_8 | spl9_12)),
% 0.21/0.53    inference(subsumption_resolution,[],[f252,f133])).
% 0.21/0.53  fof(f252,plain,(
% 0.21/0.53    v1_xboole_0(sK2) | ~m1_subset_1(sK4,sK1) | m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0) | (~spl9_2 | ~spl9_5 | spl9_7 | spl9_8)),
% 0.21/0.53    inference(resolution,[],[f171,f90])).
% 0.21/0.53  fof(f171,plain,(
% 0.21/0.53    ( ! [X2,X1] : (~r2_hidden(X2,k9_relat_1(sK3,X1)) | v1_xboole_0(X1) | ~m1_subset_1(X2,sK1) | m1_subset_1(sK6(X1,sK0,sK3,X2),sK0)) ) | (~spl9_2 | spl9_7 | spl9_8)),
% 0.21/0.53    inference(subsumption_resolution,[],[f170,f112])).
% 0.21/0.53  fof(f170,plain,(
% 0.21/0.53    ( ! [X2,X1] : (~r2_hidden(X2,k9_relat_1(sK3,X1)) | v1_xboole_0(X1) | ~m1_subset_1(X2,sK1) | m1_subset_1(sK6(X1,sK0,sK3,X2),sK0) | v1_xboole_0(sK1)) ) | (~spl9_2 | spl9_7)),
% 0.21/0.53    inference(subsumption_resolution,[],[f169,f68])).
% 0.21/0.53  fof(f169,plain,(
% 0.21/0.53    ( ! [X2,X1] : (~r2_hidden(X2,k9_relat_1(sK3,X1)) | v1_xboole_0(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X2,sK1) | m1_subset_1(sK6(X1,sK0,sK3,X2),sK0) | v1_xboole_0(sK1)) ) | (~spl9_2 | spl9_7)),
% 0.21/0.53    inference(subsumption_resolution,[],[f166,f97])).
% 0.21/0.53  fof(f166,plain,(
% 0.21/0.53    ( ! [X2,X1] : (~r2_hidden(X2,k9_relat_1(sK3,X1)) | v1_xboole_0(X1) | v1_xboole_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X2,sK1) | m1_subset_1(sK6(X1,sK0,sK3,X2),sK0) | v1_xboole_0(sK1)) ) | ~spl9_2),
% 0.21/0.53    inference(superposition,[],[f47,f75])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X4,X0) | m1_subset_1(sK6(X1,X2,X3,X4),X2) | v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f209,plain,(
% 0.21/0.53    spl9_21 | ~spl9_2 | ~spl9_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f203,f89,f67,f207])).
% 0.21/0.53  fof(f203,plain,(
% 0.21/0.53    m1_subset_1(sK4,sK1) | (~spl9_2 | ~spl9_5)),
% 0.21/0.53    inference(resolution,[],[f165,f105])).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(X0)) | m1_subset_1(sK4,X0)) ) | ~spl9_5),
% 0.21/0.53    inference(resolution,[],[f90,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.53    inference(flattening,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.53  fof(f165,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(sK1))) ) | ~spl9_2),
% 0.21/0.53    inference(superposition,[],[f74,f75])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ( ! [X3] : (m1_subset_1(k7_relset_1(sK0,sK1,sK3,X3),k1_zfmisc_1(sK1))) ) | ~spl9_2),
% 0.21/0.53    inference(resolution,[],[f68,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 0.21/0.53  fof(f179,plain,(
% 0.21/0.53    ~spl9_6 | ~spl9_15),
% 0.21/0.53    inference(avatar_split_clause,[],[f158,f152,f93])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    spl9_6 <=> v1_xboole_0(sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.21/0.53  fof(f152,plain,(
% 0.21/0.53    spl9_15 <=> r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 0.21/0.53  fof(f158,plain,(
% 0.21/0.53    ~v1_xboole_0(sK3) | ~spl9_15),
% 0.21/0.53    inference(resolution,[],[f153,f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.53  fof(f153,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3) | ~spl9_15),
% 0.21/0.53    inference(avatar_component_clause,[],[f152])).
% 0.21/0.53  fof(f154,plain,(
% 0.21/0.53    spl9_15 | ~spl9_3 | ~spl9_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f107,f89,f80,f152])).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3) | (~spl9_3 | ~spl9_5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f102,f81])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3) | ~v1_relat_1(sK3) | ~spl9_5),
% 0.21/0.53    inference(resolution,[],[f90,f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2) | ~v1_relat_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    ~spl9_12 | ~spl9_11),
% 0.21/0.53    inference(avatar_split_clause,[],[f128,f124,f132])).
% 0.21/0.53  fof(f124,plain,(
% 0.21/0.53    spl9_11 <=> r2_hidden(sK8(sK4,sK2,sK3),sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    ~v1_xboole_0(sK2) | ~spl9_11),
% 0.21/0.53    inference(resolution,[],[f125,f45])).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    r2_hidden(sK8(sK4,sK2,sK3),sK2) | ~spl9_11),
% 0.21/0.53    inference(avatar_component_clause,[],[f124])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    spl9_11 | ~spl9_3 | ~spl9_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f108,f89,f80,f124])).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    r2_hidden(sK8(sK4,sK2,sK3),sK2) | (~spl9_3 | ~spl9_5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f103,f81])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    r2_hidden(sK8(sK4,sK2,sK3),sK2) | ~v1_relat_1(sK3) | ~spl9_5),
% 0.21/0.53    inference(resolution,[],[f90,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK8(X0,X1,X2),X1) | ~v1_relat_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    spl9_6 | ~spl9_8 | ~spl9_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f72,f67,f111,f93])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    ~v1_xboole_0(sK1) | v1_xboole_0(sK3) | ~spl9_2),
% 0.21/0.53    inference(resolution,[],[f68,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0) | v1_xboole_0(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    spl9_6 | ~spl9_7 | ~spl9_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f71,f67,f96,f93])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ~v1_xboole_0(sK0) | v1_xboole_0(sK3) | ~spl9_2),
% 0.21/0.53    inference(resolution,[],[f68,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0) | v1_xboole_0(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    spl9_5 | ~spl9_2 | ~spl9_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f87,f84,f67,f89])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    spl9_4 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl9_2 | ~spl9_4)),
% 0.21/0.53    inference(forward_demodulation,[],[f85,f75])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | ~spl9_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f84])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    spl9_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f35,f84])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    spl9_3 | ~spl9_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f70,f67,f80])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    v1_relat_1(sK3) | ~spl9_2),
% 0.21/0.53    inference(resolution,[],[f68,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    spl9_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f37,f67])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    spl9_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f36,f63])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    v1_funct_1(sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (14966)------------------------------
% 0.21/0.53  % (14966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (14966)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (14966)Memory used [KB]: 6396
% 0.21/0.53  % (14966)Time elapsed: 0.086 s
% 0.21/0.53  % (14966)------------------------------
% 0.21/0.53  % (14966)------------------------------
% 0.21/0.53  % (14986)Refutation not found, incomplete strategy% (14986)------------------------------
% 0.21/0.53  % (14986)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (14986)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (14986)Memory used [KB]: 10618
% 0.21/0.53  % (14986)Time elapsed: 0.106 s
% 0.21/0.53  % (14986)------------------------------
% 0.21/0.53  % (14986)------------------------------
% 0.21/0.54  % (14965)Success in time 0.165 s
%------------------------------------------------------------------------------
