%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:34 EST 2020

% Result     : Theorem 0.11s
% Output     : Refutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 181 expanded)
%              Number of leaves         :   15 (  67 expanded)
%              Depth                    :   18
%              Number of atoms          :  306 (1350 expanded)
%              Number of equality atoms :  167 ( 763 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f134,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f47,f52,f57,f93,f109,f133])).

fof(f133,plain,
    ( spl8_1
    | spl8_2
    | spl8_3
    | ~ spl8_4
    | spl8_5
    | ~ spl8_8 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | spl8_1
    | spl8_2
    | spl8_3
    | ~ spl8_4
    | spl8_5
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f36,f41,f46,f51,f56,f108,f66])).

% (14870)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
fof(f66,plain,(
    ! [X37,X35,X33,X38,X36,X34,X32] :
      ( k3_mcart_1(X36,X37,X38) != X35
      | k7_mcart_1(X32,X33,X34,X35) = X38
      | ~ m1_subset_1(X35,k3_zfmisc_1(X32,X33,X34))
      | k1_xboole_0 = X34
      | k1_xboole_0 = X33
      | k1_xboole_0 = X32 ) ),
    inference(superposition,[],[f32,f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

fof(f32,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5)
      | X2 = X5 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5)
     => ( X2 = X5
        & X1 = X4
        & X0 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_mcart_1)).

fof(f108,plain,
    ( sK4 = k3_mcart_1(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4),sK3)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl8_8
  <=> sK4 = k3_mcart_1(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f56,plain,
    ( sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)
    | spl8_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl8_5
  <=> sK3 = k7_mcart_1(sK0,sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f51,plain,
    ( m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl8_4
  <=> m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f46,plain,
    ( k1_xboole_0 != sK2
    | spl8_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl8_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f41,plain,
    ( k1_xboole_0 != sK1
    | spl8_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f36,plain,
    ( k1_xboole_0 != sK0
    | spl8_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl8_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f109,plain,
    ( spl8_1
    | spl8_2
    | spl8_3
    | ~ spl8_4
    | spl8_8
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f95,f90,f106,f49,f44,f39,f34])).

fof(f90,plain,
    ( spl8_6
  <=> sK3 = sK7(sK0,sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f95,plain,
    ( sK4 = k3_mcart_1(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4),sK3)
    | ~ m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl8_6 ),
    inference(superposition,[],[f29,f92])).

fof(f92,plain,
    ( sK3 = sK7(sK0,sK1,sK2,sK4)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X3
            & m1_subset_1(sK7(X0,X1,X2,X3),X2)
            & m1_subset_1(sK6(X0,X1,X2,X3),X1)
            & m1_subset_1(sK5(X0,X1,X2,X3),X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f11,f17,f16,f15])).

fof(f15,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( k3_mcart_1(X4,X5,X6) = X3
                  & m1_subset_1(X6,X2) )
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,X0) )
     => ( ? [X5] :
            ( ? [X6] :
                ( k3_mcart_1(sK5(X0,X1,X2,X3),X5,X6) = X3
                & m1_subset_1(X6,X2) )
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK5(X0,X1,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( k3_mcart_1(sK5(X0,X1,X2,X3),X5,X6) = X3
              & m1_subset_1(X6,X2) )
          & m1_subset_1(X5,X1) )
     => ( ? [X6] :
            ( k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),X6) = X3
            & m1_subset_1(X6,X2) )
        & m1_subset_1(sK6(X0,X1,X2,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6] :
          ( k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),X6) = X3
          & m1_subset_1(X6,X2) )
     => ( k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X3
        & m1_subset_1(sK7(X0,X1,X2,X3),X2) ) ) ),
    introduced(choice_axiom,[])).

% (14873)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( k3_mcart_1(X4,X5,X6) = X3
                      & m1_subset_1(X6,X2) )
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,X0)
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ! [X6] :
                        ( m1_subset_1(X6,X2)
                       => k3_mcart_1(X4,X5,X6) != X3 ) ) )
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_mcart_1)).

fof(f93,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f88,f90])).

fof(f88,plain,(
    sK3 = sK7(sK0,sK1,sK2,sK4) ),
    inference(global_subsumption,[],[f21,f22,f23,f19,f87])).

fof(f87,plain,
    ( sK3 = sK7(sK0,sK1,sK2,sK4)
    | ~ m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f86])).

fof(f86,plain,
    ( sK3 = sK7(sK0,sK1,sK2,sK4)
    | ~ m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f85,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK5(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f85,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK5(X0,sK1,sK2,sK4),sK0)
      | sK3 = sK7(X0,sK1,sK2,sK4)
      | ~ m1_subset_1(sK4,k3_zfmisc_1(X0,sK1,sK2))
      | k1_xboole_0 = X0 ) ),
    inference(global_subsumption,[],[f22,f23,f84])).

fof(f84,plain,(
    ! [X0] :
      ( sK3 = sK7(X0,sK1,sK2,sK4)
      | ~ m1_subset_1(sK5(X0,sK1,sK2,sK4),sK0)
      | ~ m1_subset_1(sK4,k3_zfmisc_1(X0,sK1,sK2))
      | k1_xboole_0 = sK1
      | k1_xboole_0 = X0
      | k1_xboole_0 = sK2 ) ),
    inference(duplicate_literal_removal,[],[f83])).

% (14880)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
fof(f83,plain,(
    ! [X0] :
      ( sK3 = sK7(X0,sK1,sK2,sK4)
      | ~ m1_subset_1(sK5(X0,sK1,sK2,sK4),sK0)
      | ~ m1_subset_1(sK4,k3_zfmisc_1(X0,sK1,sK2))
      | k1_xboole_0 = sK1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(sK4,k3_zfmisc_1(X0,sK1,sK2))
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK1
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f82,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK6(X0,X1,sK2,sK4),sK1)
      | sK3 = sK7(X0,X1,sK2,sK4)
      | ~ m1_subset_1(sK5(X0,X1,sK2,sK4),sK0)
      | ~ m1_subset_1(sK4,k3_zfmisc_1(X0,X1,sK2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(global_subsumption,[],[f23,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( sK3 = sK7(X0,X1,sK2,sK4)
      | ~ m1_subset_1(sK6(X0,X1,sK2,sK4),sK1)
      | ~ m1_subset_1(sK5(X0,X1,sK2,sK4),sK0)
      | ~ m1_subset_1(sK4,k3_zfmisc_1(X0,X1,sK2))
      | k1_xboole_0 = sK2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( sK3 = sK7(X0,X1,sK2,sK4)
      | ~ m1_subset_1(sK6(X0,X1,sK2,sK4),sK1)
      | ~ m1_subset_1(sK5(X0,X1,sK2,sK4),sK0)
      | ~ m1_subset_1(sK4,k3_zfmisc_1(X0,X1,sK2))
      | k1_xboole_0 = sK2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(sK4,k3_zfmisc_1(X0,X1,sK2))
      | k1_xboole_0 = sK2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f79,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK7(X0,X1,X2,sK4),sK2)
      | sK3 = sK7(X0,X1,X2,sK4)
      | ~ m1_subset_1(sK6(X0,X1,X2,sK4),sK1)
      | ~ m1_subset_1(sK5(X0,X1,X2,sK4),sK0)
      | ~ m1_subset_1(sK4,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( sK4 != X3
      | sK3 = sK7(X0,X1,X2,X3)
      | ~ m1_subset_1(sK7(X0,X1,X2,X3),sK2)
      | ~ m1_subset_1(sK6(X0,X1,X2,X3),sK1)
      | ~ m1_subset_1(sK5(X0,X1,X2,X3),sK0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f20,f29])).

fof(f20,plain,(
    ! [X6,X7,X5] :
      ( k3_mcart_1(X5,X6,X7) != sK4
      | sK3 = X7
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK3 = X7
                | k3_mcart_1(X5,X6,X7) != sK4
                | ~ m1_subset_1(X7,sK2) )
            | ~ m1_subset_1(X6,sK1) )
        | ~ m1_subset_1(X5,sK0) )
    & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f9,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k7_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X7
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK3 = X7
                  | k3_mcart_1(X5,X6,X7) != sK4
                  | ~ m1_subset_1(X7,sK2) )
              | ~ m1_subset_1(X6,sK1) )
          | ~ m1_subset_1(X5,sK0) )
      & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X7 ) ) ) )
         => ( k7_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

% (14870)Refutation not found, incomplete strategy% (14870)------------------------------
% (14870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14870)Termination reason: Refutation not found, incomplete strategy

% (14870)Memory used [KB]: 1791
% (14870)Time elapsed: 0.125 s
% (14870)------------------------------
% (14870)------------------------------
fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X7 ) ) ) )
       => ( k7_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).

fof(f19,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f23,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f14])).

fof(f22,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

fof(f21,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f14])).

fof(f57,plain,(
    ~ spl8_5 ),
    inference(avatar_split_clause,[],[f24,f54])).

fof(f24,plain,(
    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f14])).

fof(f52,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f19,f49])).

fof(f47,plain,(
    ~ spl8_3 ),
    inference(avatar_split_clause,[],[f23,f44])).

fof(f42,plain,(
    ~ spl8_2 ),
    inference(avatar_split_clause,[],[f22,f39])).

fof(f37,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f21,f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.08  % Command    : run_vampire %s %d
% 0.08/0.26  % Computer   : n016.cluster.edu
% 0.08/0.26  % Model      : x86_64 x86_64
% 0.08/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.26  % Memory     : 8042.1875MB
% 0.08/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.26  % CPULimit   : 60
% 0.08/0.26  % WCLimit    : 600
% 0.08/0.26  % DateTime   : Tue Dec  1 09:21:19 EST 2020
% 0.08/0.26  % CPUTime    : 
% 0.11/0.40  % (14877)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.11/0.42  % (14876)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.11/0.42  % (14884)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.11/0.43  % (14892)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.11/0.43  % (14893)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.11/0.43  % (14892)Refutation found. Thanks to Tanya!
% 0.11/0.43  % SZS status Theorem for theBenchmark
% 0.11/0.43  % (14885)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.11/0.43  % (14878)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.11/0.43  % (14871)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.11/0.44  % (14894)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.11/0.44  % (14872)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.11/0.44  % (14886)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.11/0.45  % (14898)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.11/0.45  % (14883)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.11/0.45  % (14881)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.11/0.45  % (14885)Refutation not found, incomplete strategy% (14885)------------------------------
% 0.11/0.45  % (14885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.45  % (14875)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.11/0.45  % SZS output start Proof for theBenchmark
% 0.11/0.45  fof(f134,plain,(
% 0.11/0.45    $false),
% 0.11/0.45    inference(avatar_sat_refutation,[],[f37,f42,f47,f52,f57,f93,f109,f133])).
% 0.11/0.45  fof(f133,plain,(
% 0.11/0.45    spl8_1 | spl8_2 | spl8_3 | ~spl8_4 | spl8_5 | ~spl8_8),
% 0.11/0.45    inference(avatar_contradiction_clause,[],[f128])).
% 0.11/0.45  fof(f128,plain,(
% 0.11/0.45    $false | (spl8_1 | spl8_2 | spl8_3 | ~spl8_4 | spl8_5 | ~spl8_8)),
% 0.11/0.45    inference(unit_resulting_resolution,[],[f36,f41,f46,f51,f56,f108,f66])).
% 0.11/0.45  % (14870)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.11/0.45  fof(f66,plain,(
% 0.11/0.45    ( ! [X37,X35,X33,X38,X36,X34,X32] : (k3_mcart_1(X36,X37,X38) != X35 | k7_mcart_1(X32,X33,X34,X35) = X38 | ~m1_subset_1(X35,k3_zfmisc_1(X32,X33,X34)) | k1_xboole_0 = X34 | k1_xboole_0 = X33 | k1_xboole_0 = X32) )),
% 0.11/0.45    inference(superposition,[],[f32,f25])).
% 0.11/0.45  fof(f25,plain,(
% 0.11/0.45    ( ! [X2,X0,X3,X1] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.11/0.45    inference(cnf_transformation,[],[f10])).
% 0.11/0.45  fof(f10,plain,(
% 0.11/0.45    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.11/0.45    inference(ennf_transformation,[],[f5])).
% 0.11/0.45  fof(f5,axiom,(
% 0.11/0.45    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.11/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).
% 0.11/0.45  fof(f32,plain,(
% 0.11/0.45    ( ! [X4,X2,X0,X5,X3,X1] : (k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5) | X2 = X5) )),
% 0.11/0.45    inference(cnf_transformation,[],[f12])).
% 0.11/0.45  fof(f12,plain,(
% 0.11/0.45    ! [X0,X1,X2,X3,X4,X5] : ((X2 = X5 & X1 = X4 & X0 = X3) | k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5))),
% 0.11/0.45    inference(ennf_transformation,[],[f4])).
% 0.11/0.45  fof(f4,axiom,(
% 0.11/0.45    ! [X0,X1,X2,X3,X4,X5] : (k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5) => (X2 = X5 & X1 = X4 & X0 = X3))),
% 0.11/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_mcart_1)).
% 0.11/0.45  fof(f108,plain,(
% 0.11/0.45    sK4 = k3_mcart_1(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4),sK3) | ~spl8_8),
% 0.11/0.45    inference(avatar_component_clause,[],[f106])).
% 0.11/0.45  fof(f106,plain,(
% 0.11/0.45    spl8_8 <=> sK4 = k3_mcart_1(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4),sK3)),
% 0.11/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.11/0.45  fof(f56,plain,(
% 0.11/0.45    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) | spl8_5),
% 0.11/0.45    inference(avatar_component_clause,[],[f54])).
% 0.11/0.45  fof(f54,plain,(
% 0.11/0.45    spl8_5 <=> sK3 = k7_mcart_1(sK0,sK1,sK2,sK4)),
% 0.11/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.11/0.45  fof(f51,plain,(
% 0.11/0.45    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) | ~spl8_4),
% 0.11/0.45    inference(avatar_component_clause,[],[f49])).
% 0.11/0.45  fof(f49,plain,(
% 0.11/0.45    spl8_4 <=> m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.11/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.11/0.45  fof(f46,plain,(
% 0.11/0.45    k1_xboole_0 != sK2 | spl8_3),
% 0.11/0.45    inference(avatar_component_clause,[],[f44])).
% 0.11/0.45  fof(f44,plain,(
% 0.11/0.45    spl8_3 <=> k1_xboole_0 = sK2),
% 0.11/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.11/0.45  fof(f41,plain,(
% 0.11/0.45    k1_xboole_0 != sK1 | spl8_2),
% 0.11/0.45    inference(avatar_component_clause,[],[f39])).
% 0.11/0.45  fof(f39,plain,(
% 0.11/0.45    spl8_2 <=> k1_xboole_0 = sK1),
% 0.11/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.11/0.45  fof(f36,plain,(
% 0.11/0.45    k1_xboole_0 != sK0 | spl8_1),
% 0.11/0.45    inference(avatar_component_clause,[],[f34])).
% 0.11/0.45  fof(f34,plain,(
% 0.11/0.45    spl8_1 <=> k1_xboole_0 = sK0),
% 0.11/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.11/0.45  fof(f109,plain,(
% 0.11/0.45    spl8_1 | spl8_2 | spl8_3 | ~spl8_4 | spl8_8 | ~spl8_6),
% 0.11/0.45    inference(avatar_split_clause,[],[f95,f90,f106,f49,f44,f39,f34])).
% 0.11/0.45  fof(f90,plain,(
% 0.11/0.45    spl8_6 <=> sK3 = sK7(sK0,sK1,sK2,sK4)),
% 0.11/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.11/0.45  fof(f95,plain,(
% 0.11/0.45    sK4 = k3_mcart_1(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4),sK3) | ~m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl8_6),
% 0.11/0.45    inference(superposition,[],[f29,f92])).
% 0.11/0.45  fof(f92,plain,(
% 0.11/0.45    sK3 = sK7(sK0,sK1,sK2,sK4) | ~spl8_6),
% 0.11/0.45    inference(avatar_component_clause,[],[f90])).
% 0.11/0.45  fof(f29,plain,(
% 0.11/0.45    ( ! [X2,X0,X3,X1] : (k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.11/0.45    inference(cnf_transformation,[],[f18])).
% 0.11/0.45  fof(f18,plain,(
% 0.11/0.45    ! [X0,X1,X2] : (! [X3] : ((((k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X3 & m1_subset_1(sK7(X0,X1,X2,X3),X2)) & m1_subset_1(sK6(X0,X1,X2,X3),X1)) & m1_subset_1(sK5(X0,X1,X2,X3),X0)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.11/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f11,f17,f16,f15])).
% 0.11/0.45  fof(f15,plain,(
% 0.11/0.45    ! [X3,X2,X1,X0] : (? [X4] : (? [X5] : (? [X6] : (k3_mcart_1(X4,X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) => (? [X5] : (? [X6] : (k3_mcart_1(sK5(X0,X1,X2,X3),X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(sK5(X0,X1,X2,X3),X0)))),
% 0.11/0.45    introduced(choice_axiom,[])).
% 0.11/0.45  fof(f16,plain,(
% 0.11/0.45    ! [X3,X2,X1,X0] : (? [X5] : (? [X6] : (k3_mcart_1(sK5(X0,X1,X2,X3),X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) => (? [X6] : (k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(sK6(X0,X1,X2,X3),X1)))),
% 0.11/0.45    introduced(choice_axiom,[])).
% 0.11/0.45  fof(f17,plain,(
% 0.11/0.45    ! [X3,X2,X1,X0] : (? [X6] : (k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),X6) = X3 & m1_subset_1(X6,X2)) => (k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X3 & m1_subset_1(sK7(X0,X1,X2,X3),X2)))),
% 0.11/0.45    introduced(choice_axiom,[])).
% 0.11/0.45  % (14873)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.11/0.45  fof(f11,plain,(
% 0.11/0.45    ! [X0,X1,X2] : (! [X3] : (? [X4] : (? [X5] : (? [X6] : (k3_mcart_1(X4,X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.11/0.45    inference(ennf_transformation,[],[f3])).
% 0.11/0.45  fof(f3,axiom,(
% 0.11/0.45    ! [X0,X1,X2] : ~(? [X3] : (! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => ! [X6] : (m1_subset_1(X6,X2) => k3_mcart_1(X4,X5,X6) != X3))) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.11/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_mcart_1)).
% 0.11/0.45  fof(f93,plain,(
% 0.11/0.45    spl8_6),
% 0.11/0.45    inference(avatar_split_clause,[],[f88,f90])).
% 0.11/0.45  fof(f88,plain,(
% 0.11/0.45    sK3 = sK7(sK0,sK1,sK2,sK4)),
% 0.11/0.45    inference(global_subsumption,[],[f21,f22,f23,f19,f87])).
% 0.11/0.45  fof(f87,plain,(
% 0.11/0.45    sK3 = sK7(sK0,sK1,sK2,sK4) | ~m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 0.11/0.45    inference(duplicate_literal_removal,[],[f86])).
% 0.11/0.45  fof(f86,plain,(
% 0.11/0.45    sK3 = sK7(sK0,sK1,sK2,sK4) | ~m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK0 | ~m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.11/0.45    inference(resolution,[],[f85,f26])).
% 0.11/0.45  fof(f26,plain,(
% 0.11/0.45    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK5(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.11/0.45    inference(cnf_transformation,[],[f18])).
% 0.11/0.45  fof(f85,plain,(
% 0.11/0.45    ( ! [X0] : (~m1_subset_1(sK5(X0,sK1,sK2,sK4),sK0) | sK3 = sK7(X0,sK1,sK2,sK4) | ~m1_subset_1(sK4,k3_zfmisc_1(X0,sK1,sK2)) | k1_xboole_0 = X0) )),
% 0.11/0.45    inference(global_subsumption,[],[f22,f23,f84])).
% 0.11/0.45  fof(f84,plain,(
% 0.11/0.45    ( ! [X0] : (sK3 = sK7(X0,sK1,sK2,sK4) | ~m1_subset_1(sK5(X0,sK1,sK2,sK4),sK0) | ~m1_subset_1(sK4,k3_zfmisc_1(X0,sK1,sK2)) | k1_xboole_0 = sK1 | k1_xboole_0 = X0 | k1_xboole_0 = sK2) )),
% 0.11/0.45    inference(duplicate_literal_removal,[],[f83])).
% 0.11/0.45  % (14880)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.11/0.45  fof(f83,plain,(
% 0.11/0.45    ( ! [X0] : (sK3 = sK7(X0,sK1,sK2,sK4) | ~m1_subset_1(sK5(X0,sK1,sK2,sK4),sK0) | ~m1_subset_1(sK4,k3_zfmisc_1(X0,sK1,sK2)) | k1_xboole_0 = sK1 | k1_xboole_0 = X0 | ~m1_subset_1(sK4,k3_zfmisc_1(X0,sK1,sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = X0) )),
% 0.11/0.45    inference(resolution,[],[f82,f27])).
% 0.11/0.45  fof(f27,plain,(
% 0.11/0.45    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK6(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.11/0.45    inference(cnf_transformation,[],[f18])).
% 0.11/0.45  fof(f82,plain,(
% 0.11/0.45    ( ! [X0,X1] : (~m1_subset_1(sK6(X0,X1,sK2,sK4),sK1) | sK3 = sK7(X0,X1,sK2,sK4) | ~m1_subset_1(sK5(X0,X1,sK2,sK4),sK0) | ~m1_subset_1(sK4,k3_zfmisc_1(X0,X1,sK2)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.11/0.45    inference(global_subsumption,[],[f23,f81])).
% 0.11/0.45  fof(f81,plain,(
% 0.11/0.45    ( ! [X0,X1] : (sK3 = sK7(X0,X1,sK2,sK4) | ~m1_subset_1(sK6(X0,X1,sK2,sK4),sK1) | ~m1_subset_1(sK5(X0,X1,sK2,sK4),sK0) | ~m1_subset_1(sK4,k3_zfmisc_1(X0,X1,sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.11/0.45    inference(duplicate_literal_removal,[],[f80])).
% 0.11/0.45  fof(f80,plain,(
% 0.11/0.45    ( ! [X0,X1] : (sK3 = sK7(X0,X1,sK2,sK4) | ~m1_subset_1(sK6(X0,X1,sK2,sK4),sK1) | ~m1_subset_1(sK5(X0,X1,sK2,sK4),sK0) | ~m1_subset_1(sK4,k3_zfmisc_1(X0,X1,sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(sK4,k3_zfmisc_1(X0,X1,sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.11/0.45    inference(resolution,[],[f79,f28])).
% 0.11/0.45  fof(f28,plain,(
% 0.11/0.45    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK7(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.11/0.45    inference(cnf_transformation,[],[f18])).
% 0.11/0.45  fof(f79,plain,(
% 0.11/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(sK7(X0,X1,X2,sK4),sK2) | sK3 = sK7(X0,X1,X2,sK4) | ~m1_subset_1(sK6(X0,X1,X2,sK4),sK1) | ~m1_subset_1(sK5(X0,X1,X2,sK4),sK0) | ~m1_subset_1(sK4,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.11/0.45    inference(equality_resolution,[],[f71])).
% 0.11/0.45  fof(f71,plain,(
% 0.11/0.45    ( ! [X2,X0,X3,X1] : (sK4 != X3 | sK3 = sK7(X0,X1,X2,X3) | ~m1_subset_1(sK7(X0,X1,X2,X3),sK2) | ~m1_subset_1(sK6(X0,X1,X2,X3),sK1) | ~m1_subset_1(sK5(X0,X1,X2,X3),sK0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.11/0.45    inference(superposition,[],[f20,f29])).
% 0.11/0.45  fof(f20,plain,(
% 0.11/0.45    ( ! [X6,X7,X5] : (k3_mcart_1(X5,X6,X7) != sK4 | sK3 = X7 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 0.11/0.45    inference(cnf_transformation,[],[f14])).
% 0.11/0.45  fof(f14,plain,(
% 0.11/0.45    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.11/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f9,f13])).
% 0.11/0.45  fof(f13,plain,(
% 0.11/0.45    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)))),
% 0.11/0.45    introduced(choice_axiom,[])).
% 0.11/0.45  fof(f9,plain,(
% 0.11/0.45    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.11/0.45    inference(flattening,[],[f8])).
% 0.11/0.45  fof(f8,plain,(
% 0.11/0.45    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.11/0.45    inference(ennf_transformation,[],[f7])).
% 0.11/0.45  fof(f7,negated_conjecture,(
% 0.11/0.45    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.11/0.45    inference(negated_conjecture,[],[f6])).
% 0.11/0.45  % (14870)Refutation not found, incomplete strategy% (14870)------------------------------
% 0.11/0.45  % (14870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.45  % (14870)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.45  
% 0.11/0.45  % (14870)Memory used [KB]: 1791
% 0.11/0.45  % (14870)Time elapsed: 0.125 s
% 0.11/0.45  % (14870)------------------------------
% 0.11/0.45  % (14870)------------------------------
% 0.11/0.45  fof(f6,conjecture,(
% 0.11/0.45    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.11/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).
% 0.11/0.45  fof(f19,plain,(
% 0.11/0.45    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.11/0.45    inference(cnf_transformation,[],[f14])).
% 0.11/0.45  fof(f23,plain,(
% 0.11/0.45    k1_xboole_0 != sK2),
% 0.11/0.45    inference(cnf_transformation,[],[f14])).
% 0.11/0.45  fof(f22,plain,(
% 0.11/0.45    k1_xboole_0 != sK1),
% 0.11/0.45    inference(cnf_transformation,[],[f14])).
% 0.11/0.45  fof(f21,plain,(
% 0.11/0.45    k1_xboole_0 != sK0),
% 0.11/0.45    inference(cnf_transformation,[],[f14])).
% 0.11/0.45  fof(f57,plain,(
% 0.11/0.45    ~spl8_5),
% 0.11/0.45    inference(avatar_split_clause,[],[f24,f54])).
% 0.11/0.45  fof(f24,plain,(
% 0.11/0.45    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)),
% 0.11/0.45    inference(cnf_transformation,[],[f14])).
% 0.11/0.45  fof(f52,plain,(
% 0.11/0.45    spl8_4),
% 0.11/0.45    inference(avatar_split_clause,[],[f19,f49])).
% 0.11/0.45  fof(f47,plain,(
% 0.11/0.45    ~spl8_3),
% 0.11/0.45    inference(avatar_split_clause,[],[f23,f44])).
% 0.11/0.45  fof(f42,plain,(
% 0.11/0.45    ~spl8_2),
% 0.11/0.45    inference(avatar_split_clause,[],[f22,f39])).
% 0.11/0.45  fof(f37,plain,(
% 0.11/0.45    ~spl8_1),
% 0.11/0.45    inference(avatar_split_clause,[],[f21,f34])).
% 0.11/0.45  % SZS output end Proof for theBenchmark
% 0.11/0.45  % (14892)------------------------------
% 0.11/0.45  % (14892)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.45  % (14892)Termination reason: Refutation
% 0.11/0.45  
% 0.11/0.45  % (14892)Memory used [KB]: 10874
% 0.11/0.45  % (14892)Time elapsed: 0.110 s
% 0.11/0.45  % (14892)------------------------------
% 0.11/0.45  % (14892)------------------------------
% 0.11/0.45  % (14842)Success in time 0.176 s
%------------------------------------------------------------------------------
