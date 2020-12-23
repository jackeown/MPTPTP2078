%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 172 expanded)
%              Number of leaves         :   22 (  73 expanded)
%              Depth                    :   16
%              Number of atoms          :  452 (1059 expanded)
%              Number of equality atoms :   63 ( 195 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f214,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f103,f108,f113,f118,f123,f128,f133,f139,f158,f163,f202,f213])).

fof(f213,plain,
    ( ~ spl9_18
    | ~ spl9_3
    | ~ spl9_5
    | spl9_12 ),
    inference(avatar_split_clause,[],[f212,f155,f110,f100,f199])).

fof(f199,plain,
    ( spl9_18
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f100,plain,
    ( spl9_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f110,plain,
    ( spl9_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f155,plain,
    ( spl9_12
  <=> v1_partfun1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f212,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl9_3
    | ~ spl9_5
    | spl9_12 ),
    inference(forward_demodulation,[],[f164,f102])).

fof(f102,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f100])).

fof(f164,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl9_5
    | spl9_12 ),
    inference(subsumption_resolution,[],[f160,f157])).

fof(f157,plain,
    ( ~ v1_partfun1(sK3,sK0)
    | spl9_12 ),
    inference(avatar_component_clause,[],[f155])).

fof(f160,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ v1_xboole_0(sK0)
    | ~ spl9_5 ),
    inference(resolution,[],[f112,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_partfun1(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

fof(f112,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f110])).

fof(f202,plain,
    ( spl9_18
    | ~ spl9_2
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f196,f136,f96,f199])).

fof(f96,plain,
    ( spl9_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f136,plain,
    ( spl9_10
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f196,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl9_2
    | ~ spl9_10 ),
    inference(backward_demodulation,[],[f137,f97])).

fof(f97,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f137,plain,
    ( v1_xboole_0(sK1)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f136])).

fof(f163,plain,
    ( ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | spl9_10
    | spl9_12 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | spl9_10
    | spl9_12 ),
    inference(subsumption_resolution,[],[f159,f157])).

fof(f159,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | spl9_10 ),
    inference(unit_resulting_resolution,[],[f122,f138,f117,f112,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X1)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f117,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl9_6
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f138,plain,
    ( ~ v1_xboole_0(sK1)
    | spl9_10 ),
    inference(avatar_component_clause,[],[f136])).

fof(f122,plain,
    ( v1_funct_1(sK3)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl9_7
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f158,plain,
    ( ~ spl9_12
    | spl9_1
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9 ),
    inference(avatar_split_clause,[],[f153,f130,f125,f120,f110,f105,f91,f155])).

fof(f91,plain,
    ( spl9_1
  <=> r2_hidden(sK3,k5_partfun1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f105,plain,
    ( spl9_4
  <=> r1_partfun1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f125,plain,
    ( spl9_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f130,plain,
    ( spl9_9
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f153,plain,
    ( ~ v1_partfun1(sK3,sK0)
    | spl9_1
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f152,f132])).

fof(f132,plain,
    ( v1_funct_1(sK2)
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f130])).

fof(f152,plain,
    ( ~ v1_partfun1(sK3,sK0)
    | ~ v1_funct_1(sK2)
    | spl9_1
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f151,f127])).

fof(f127,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f125])).

fof(f151,plain,
    ( ~ v1_partfun1(sK3,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl9_1
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f150,f122])).

fof(f150,plain,
    ( ~ v1_partfun1(sK3,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl9_1
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f149,f112])).

fof(f149,plain,
    ( ~ v1_partfun1(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl9_1
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f148,f107])).

fof(f107,plain,
    ( r1_partfun1(sK2,sK3)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f105])).

fof(f148,plain,
    ( ~ r1_partfun1(sK2,sK3)
    | ~ v1_partfun1(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl9_1 ),
    inference(resolution,[],[f93,f84])).

fof(f84,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(X8,k5_partfun1(X0,X1,X2))
      | ~ r1_partfun1(X2,X8)
      | ~ v1_partfun1(X8,X0)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X8,X3,X1] :
      ( r2_hidden(X8,X3)
      | ~ r1_partfun1(X2,X8)
      | ~ v1_partfun1(X8,X0)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X8)
      | k5_partfun1(X0,X1,X2) != X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X8,X7,X3,X1] :
      ( r2_hidden(X7,X3)
      | ~ r1_partfun1(X2,X8)
      | ~ v1_partfun1(X8,X0)
      | X7 != X8
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X8)
      | k5_partfun1(X0,X1,X2) != X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ( ( ! [X5] :
                    ( ~ r1_partfun1(X2,X5)
                    | ~ v1_partfun1(X5,X0)
                    | sK5(X0,X1,X2,X3) != X5
                    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    | ~ v1_funct_1(X5) )
                | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
              & ( ( r1_partfun1(X2,sK6(X0,X1,X2,X3))
                  & v1_partfun1(sK6(X0,X1,X2,X3),X0)
                  & sK5(X0,X1,X2,X3) = sK6(X0,X1,X2,X3)
                  & m1_subset_1(sK6(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(sK6(X0,X1,X2,X3)) )
                | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) )
          & ( ! [X7] :
                ( ( r2_hidden(X7,X3)
                  | ! [X8] :
                      ( ~ r1_partfun1(X2,X8)
                      | ~ v1_partfun1(X8,X0)
                      | X7 != X8
                      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_1(X8) ) )
                & ( ( r1_partfun1(X2,sK7(X0,X1,X2,X7))
                    & v1_partfun1(sK7(X0,X1,X2,X7),X0)
                    & sK7(X0,X1,X2,X7) = X7
                    & m1_subset_1(sK7(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_1(sK7(X0,X1,X2,X7)) )
                  | ~ r2_hidden(X7,X3) ) )
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f43,f46,f45,f44])).

fof(f44,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r1_partfun1(X2,X5)
                | ~ v1_partfun1(X5,X0)
                | X4 != X5
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                | ~ v1_funct_1(X5) )
            | ~ r2_hidden(X4,X3) )
          & ( ? [X6] :
                ( r1_partfun1(X2,X6)
                & v1_partfun1(X6,X0)
                & X4 = X6
                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_1(X6) )
            | r2_hidden(X4,X3) ) )
     => ( ( ! [X5] :
              ( ~ r1_partfun1(X2,X5)
              | ~ v1_partfun1(X5,X0)
              | sK5(X0,X1,X2,X3) != X5
              | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_1(X5) )
          | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
        & ( ? [X6] :
              ( r1_partfun1(X2,X6)
              & v1_partfun1(X6,X0)
              & sK5(X0,X1,X2,X3) = X6
              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X6) )
          | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6] :
          ( r1_partfun1(X2,X6)
          & v1_partfun1(X6,X0)
          & sK5(X0,X1,X2,X3) = X6
          & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X6) )
     => ( r1_partfun1(X2,sK6(X0,X1,X2,X3))
        & v1_partfun1(sK6(X0,X1,X2,X3),X0)
        & sK5(X0,X1,X2,X3) = sK6(X0,X1,X2,X3)
        & m1_subset_1(sK6(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(sK6(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X7,X2,X1,X0] :
      ( ? [X9] :
          ( r1_partfun1(X2,X9)
          & v1_partfun1(X9,X0)
          & X7 = X9
          & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X9) )
     => ( r1_partfun1(X2,sK7(X0,X1,X2,X7))
        & v1_partfun1(sK7(X0,X1,X2,X7),X0)
        & sK7(X0,X1,X2,X7) = X7
        & m1_subset_1(sK7(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(sK7(X0,X1,X2,X7)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ? [X4] :
                ( ( ! [X5] :
                      ( ~ r1_partfun1(X2,X5)
                      | ~ v1_partfun1(X5,X0)
                      | X4 != X5
                      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_1(X5) )
                  | ~ r2_hidden(X4,X3) )
                & ( ? [X6] :
                      ( r1_partfun1(X2,X6)
                      & v1_partfun1(X6,X0)
                      & X4 = X6
                      & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      & v1_funct_1(X6) )
                  | r2_hidden(X4,X3) ) ) )
          & ( ! [X7] :
                ( ( r2_hidden(X7,X3)
                  | ! [X8] :
                      ( ~ r1_partfun1(X2,X8)
                      | ~ v1_partfun1(X8,X0)
                      | X7 != X8
                      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_1(X8) ) )
                & ( ? [X9] :
                      ( r1_partfun1(X2,X9)
                      & v1_partfun1(X9,X0)
                      & X7 = X9
                      & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      & v1_funct_1(X9) )
                  | ~ r2_hidden(X7,X3) ) )
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ? [X4] :
                ( ( ! [X5] :
                      ( ~ r1_partfun1(X2,X5)
                      | ~ v1_partfun1(X5,X0)
                      | X4 != X5
                      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_1(X5) )
                  | ~ r2_hidden(X4,X3) )
                & ( ? [X5] :
                      ( r1_partfun1(X2,X5)
                      & v1_partfun1(X5,X0)
                      & X4 = X5
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      & v1_funct_1(X5) )
                  | r2_hidden(X4,X3) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X3)
                  | ! [X5] :
                      ( ~ r1_partfun1(X2,X5)
                      | ~ v1_partfun1(X5,X0)
                      | X4 != X5
                      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_1(X5) ) )
                & ( ? [X5] :
                      ( r1_partfun1(X2,X5)
                      & v1_partfun1(X5,X0)
                      & X4 = X5
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      & v1_funct_1(X5) )
                  | ~ r2_hidden(X4,X3) ) )
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_partfun1)).

fof(f93,plain,
    ( ~ r2_hidden(sK3,k5_partfun1(sK0,sK1,sK2))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f139,plain,
    ( ~ spl9_10
    | spl9_2 ),
    inference(avatar_split_clause,[],[f134,f96,f136])).

fof(f134,plain,
    ( ~ v1_xboole_0(sK1)
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f98,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f98,plain,
    ( k1_xboole_0 != sK1
    | spl9_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f133,plain,(
    spl9_9 ),
    inference(avatar_split_clause,[],[f52,f130])).

fof(f52,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ~ r2_hidden(sK3,k5_partfun1(sK0,sK1,sK2))
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_partfun1(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f38,f37])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
            & ( k1_xboole_0 = X0
              | k1_xboole_0 != X1 )
            & r1_partfun1(X2,X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_hidden(X3,k5_partfun1(sK0,sK1,sK2))
          & ( k1_xboole_0 = sK0
            | k1_xboole_0 != sK1 )
          & r1_partfun1(sK2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X3,sK0,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X3] :
        ( ~ r2_hidden(X3,k5_partfun1(sK0,sK1,sK2))
        & ( k1_xboole_0 = sK0
          | k1_xboole_0 != sK1 )
        & r1_partfun1(sK2,X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X3,sK0,sK1)
        & v1_funct_1(X3) )
   => ( ~ r2_hidden(sK3,k5_partfun1(sK0,sK1,sK2))
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_partfun1(sK2,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( r1_partfun1(X2,X3)
             => ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
                | ( k1_xboole_0 != X0
                  & k1_xboole_0 = X1 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_2)).

fof(f128,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f53,f125])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f123,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f54,f120])).

fof(f54,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f118,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f55,f115])).

fof(f55,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f113,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f56,f110])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f108,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f57,f105])).

fof(f57,plain,(
    r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f103,plain,
    ( ~ spl9_2
    | spl9_3 ),
    inference(avatar_split_clause,[],[f58,f100,f96])).

fof(f58,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f39])).

fof(f94,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f59,f91])).

fof(f59,plain,(
    ~ r2_hidden(sK3,k5_partfun1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:03:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (1416)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.48  % (1424)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (1424)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f214,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f94,f103,f108,f113,f118,f123,f128,f133,f139,f158,f163,f202,f213])).
% 0.21/0.50  fof(f213,plain,(
% 0.21/0.50    ~spl9_18 | ~spl9_3 | ~spl9_5 | spl9_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f212,f155,f110,f100,f199])).
% 0.21/0.50  fof(f199,plain,(
% 0.21/0.50    spl9_18 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    spl9_3 <=> k1_xboole_0 = sK0),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    spl9_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.21/0.50  fof(f155,plain,(
% 0.21/0.50    spl9_12 <=> v1_partfun1(sK3,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 0.21/0.50  fof(f212,plain,(
% 0.21/0.50    ~v1_xboole_0(k1_xboole_0) | (~spl9_3 | ~spl9_5 | spl9_12)),
% 0.21/0.50    inference(forward_demodulation,[],[f164,f102])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    k1_xboole_0 = sK0 | ~spl9_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f100])).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    ~v1_xboole_0(sK0) | (~spl9_5 | spl9_12)),
% 0.21/0.50    inference(subsumption_resolution,[],[f160,f157])).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    ~v1_partfun1(sK3,sK0) | spl9_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f155])).
% 0.21/0.50  fof(f160,plain,(
% 0.21/0.50    v1_partfun1(sK3,sK0) | ~v1_xboole_0(sK0) | ~spl9_5),
% 0.21/0.50    inference(resolution,[],[f112,f76])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_partfun1(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl9_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f110])).
% 0.21/0.50  fof(f202,plain,(
% 0.21/0.50    spl9_18 | ~spl9_2 | ~spl9_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f196,f136,f96,f199])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    spl9_2 <=> k1_xboole_0 = sK1),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    spl9_10 <=> v1_xboole_0(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 0.21/0.50  fof(f196,plain,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0) | (~spl9_2 | ~spl9_10)),
% 0.21/0.50    inference(backward_demodulation,[],[f137,f97])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | ~spl9_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f96])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    v1_xboole_0(sK1) | ~spl9_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f136])).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    ~spl9_5 | ~spl9_6 | ~spl9_7 | spl9_10 | spl9_12),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f162])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    $false | (~spl9_5 | ~spl9_6 | ~spl9_7 | spl9_10 | spl9_12)),
% 0.21/0.50    inference(subsumption_resolution,[],[f159,f157])).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    v1_partfun1(sK3,sK0) | (~spl9_5 | ~spl9_6 | ~spl9_7 | spl9_10)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f122,f138,f117,f112,f75])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v1_xboole_0(X1) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_partfun1(X2,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.50    inference(flattening,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,axiom,(
% 0.21/0.50    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    v1_funct_2(sK3,sK0,sK1) | ~spl9_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f115])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    spl9_6 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    ~v1_xboole_0(sK1) | spl9_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f136])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    v1_funct_1(sK3) | ~spl9_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f120])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    spl9_7 <=> v1_funct_1(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    ~spl9_12 | spl9_1 | ~spl9_4 | ~spl9_5 | ~spl9_7 | ~spl9_8 | ~spl9_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f153,f130,f125,f120,f110,f105,f91,f155])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    spl9_1 <=> r2_hidden(sK3,k5_partfun1(sK0,sK1,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    spl9_4 <=> r1_partfun1(sK2,sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    spl9_8 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    spl9_9 <=> v1_funct_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.21/0.50  fof(f153,plain,(
% 0.21/0.50    ~v1_partfun1(sK3,sK0) | (spl9_1 | ~spl9_4 | ~spl9_5 | ~spl9_7 | ~spl9_8 | ~spl9_9)),
% 0.21/0.50    inference(subsumption_resolution,[],[f152,f132])).
% 0.21/0.50  fof(f132,plain,(
% 0.21/0.50    v1_funct_1(sK2) | ~spl9_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f130])).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    ~v1_partfun1(sK3,sK0) | ~v1_funct_1(sK2) | (spl9_1 | ~spl9_4 | ~spl9_5 | ~spl9_7 | ~spl9_8)),
% 0.21/0.50    inference(subsumption_resolution,[],[f151,f127])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl9_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f125])).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    ~v1_partfun1(sK3,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (spl9_1 | ~spl9_4 | ~spl9_5 | ~spl9_7)),
% 0.21/0.50    inference(subsumption_resolution,[],[f150,f122])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    ~v1_partfun1(sK3,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (spl9_1 | ~spl9_4 | ~spl9_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f149,f112])).
% 0.21/0.50  fof(f149,plain,(
% 0.21/0.50    ~v1_partfun1(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (spl9_1 | ~spl9_4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f148,f107])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    r1_partfun1(sK2,sK3) | ~spl9_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f105])).
% 0.21/0.50  fof(f148,plain,(
% 0.21/0.50    ~r1_partfun1(sK2,sK3) | ~v1_partfun1(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl9_1),
% 0.21/0.50    inference(resolution,[],[f93,f84])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    ( ! [X2,X0,X8,X1] : (r2_hidden(X8,k5_partfun1(X0,X1,X2)) | ~r1_partfun1(X2,X8) | ~v1_partfun1(X8,X0) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X8) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.50    inference(equality_resolution,[],[f83])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    ( ! [X2,X0,X8,X3,X1] : (r2_hidden(X8,X3) | ~r1_partfun1(X2,X8) | ~v1_partfun1(X8,X0) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X8) | k5_partfun1(X0,X1,X2) != X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.50    inference(equality_resolution,[],[f67])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X2,X0,X8,X7,X3,X1] : (r2_hidden(X7,X3) | ~r1_partfun1(X2,X8) | ~v1_partfun1(X8,X0) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X8) | k5_partfun1(X0,X1,X2) != X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (! [X3] : ((k5_partfun1(X0,X1,X2) = X3 | ((! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | sK5(X0,X1,X2,X3) != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5)) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & ((r1_partfun1(X2,sK6(X0,X1,X2,X3)) & v1_partfun1(sK6(X0,X1,X2,X3),X0) & sK5(X0,X1,X2,X3) = sK6(X0,X1,X2,X3) & m1_subset_1(sK6(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(sK6(X0,X1,X2,X3))) | r2_hidden(sK5(X0,X1,X2,X3),X3)))) & (! [X7] : ((r2_hidden(X7,X3) | ! [X8] : (~r1_partfun1(X2,X8) | ~v1_partfun1(X8,X0) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X8))) & ((r1_partfun1(X2,sK7(X0,X1,X2,X7)) & v1_partfun1(sK7(X0,X1,X2,X7),X0) & sK7(X0,X1,X2,X7) = X7 & m1_subset_1(sK7(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(sK7(X0,X1,X2,X7))) | ~r2_hidden(X7,X3))) | k5_partfun1(X0,X1,X2) != X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f43,f46,f45,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ! [X3,X2,X1,X0] : (? [X4] : ((! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X6] : (r1_partfun1(X2,X6) & v1_partfun1(X6,X0) & X4 = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X6)) | r2_hidden(X4,X3))) => ((! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | sK5(X0,X1,X2,X3) != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5)) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (? [X6] : (r1_partfun1(X2,X6) & v1_partfun1(X6,X0) & sK5(X0,X1,X2,X3) = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X6)) | r2_hidden(sK5(X0,X1,X2,X3),X3))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ! [X3,X2,X1,X0] : (? [X6] : (r1_partfun1(X2,X6) & v1_partfun1(X6,X0) & sK5(X0,X1,X2,X3) = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X6)) => (r1_partfun1(X2,sK6(X0,X1,X2,X3)) & v1_partfun1(sK6(X0,X1,X2,X3),X0) & sK5(X0,X1,X2,X3) = sK6(X0,X1,X2,X3) & m1_subset_1(sK6(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(sK6(X0,X1,X2,X3))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ! [X7,X2,X1,X0] : (? [X9] : (r1_partfun1(X2,X9) & v1_partfun1(X9,X0) & X7 = X9 & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X9)) => (r1_partfun1(X2,sK7(X0,X1,X2,X7)) & v1_partfun1(sK7(X0,X1,X2,X7),X0) & sK7(X0,X1,X2,X7) = X7 & m1_subset_1(sK7(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(sK7(X0,X1,X2,X7))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (! [X3] : ((k5_partfun1(X0,X1,X2) = X3 | ? [X4] : ((! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X6] : (r1_partfun1(X2,X6) & v1_partfun1(X6,X0) & X4 = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X6)) | r2_hidden(X4,X3)))) & (! [X7] : ((r2_hidden(X7,X3) | ! [X8] : (~r1_partfun1(X2,X8) | ~v1_partfun1(X8,X0) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X8))) & (? [X9] : (r1_partfun1(X2,X9) & v1_partfun1(X9,X0) & X7 = X9 & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X9)) | ~r2_hidden(X7,X3))) | k5_partfun1(X0,X1,X2) != X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.50    inference(rectify,[],[f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (! [X3] : ((k5_partfun1(X0,X1,X2) = X3 | ? [X4] : ((! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5))) & (? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)) | ~r2_hidden(X4,X3))) | k5_partfun1(X0,X1,X2) != X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.50    inference(nnf_transformation,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.50    inference(flattening,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_partfun1)).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    ~r2_hidden(sK3,k5_partfun1(sK0,sK1,sK2)) | spl9_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f91])).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    ~spl9_10 | spl9_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f134,f96,f136])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    ~v1_xboole_0(sK1) | spl9_2),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f98,f81])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    k1_xboole_0 != sK1 | spl9_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f96])).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    spl9_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f52,f130])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    v1_funct_1(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    (~r2_hidden(sK3,k5_partfun1(sK0,sK1,sK2)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f38,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (? [X3] : (~r2_hidden(X3,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (~r2_hidden(X3,k5_partfun1(sK0,sK1,sK2)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ? [X3] : (~r2_hidden(X3,k5_partfun1(sK0,sK1,sK2)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) => (~r2_hidden(sK3,k5_partfun1(sK0,sK1,sK2)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (? [X3] : (~r2_hidden(X3,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.21/0.50    inference(flattening,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (? [X3] : (((~r2_hidden(X3,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.21/0.50    inference(negated_conjecture,[],[f23])).
% 0.21/0.50  fof(f23,conjecture,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_2)).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    spl9_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f53,f125])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    inference(cnf_transformation,[],[f39])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    spl9_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f54,f120])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    v1_funct_1(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f39])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    spl9_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f55,f115])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f39])).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    spl9_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f56,f110])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    inference(cnf_transformation,[],[f39])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    spl9_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f57,f105])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    r1_partfun1(sK2,sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f39])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    ~spl9_2 | spl9_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f58,f100,f96])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.21/0.50    inference(cnf_transformation,[],[f39])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    ~spl9_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f59,f91])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ~r2_hidden(sK3,k5_partfun1(sK0,sK1,sK2))),
% 0.21/0.50    inference(cnf_transformation,[],[f39])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (1424)------------------------------
% 0.21/0.50  % (1424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (1424)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (1424)Memory used [KB]: 6268
% 0.21/0.50  % (1424)Time elapsed: 0.084 s
% 0.21/0.50  % (1424)------------------------------
% 0.21/0.50  % (1424)------------------------------
% 0.21/0.50  % (1410)Success in time 0.144 s
%------------------------------------------------------------------------------
