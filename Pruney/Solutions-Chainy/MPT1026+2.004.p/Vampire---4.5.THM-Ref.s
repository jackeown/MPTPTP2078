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
% DateTime   : Thu Dec  3 13:06:31 EST 2020

% Result     : Theorem 1.86s
% Output     : Refutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 697 expanded)
%              Number of leaves         :   32 ( 242 expanded)
%              Depth                    :   15
%              Number of atoms          :  502 (5632 expanded)
%              Number of equality atoms :   92 (1721 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1008,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f135,f156,f220,f237,f628,f948])).

fof(f948,plain,
    ( ~ spl10_1
    | spl10_2
    | ~ spl10_3
    | ~ spl10_5 ),
    inference(avatar_contradiction_clause,[],[f947])).

fof(f947,plain,
    ( $false
    | ~ spl10_1
    | spl10_2
    | ~ spl10_3
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f854,f67])).

fof(f67,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f854,plain,
    ( ~ r1_tarski(k1_xboole_0,sK4(k1_xboole_0))
    | ~ spl10_1
    | spl10_2
    | ~ spl10_3
    | ~ spl10_5 ),
    inference(backward_demodulation,[],[f417,f215])).

fof(f215,plain,
    ( k1_xboole_0 = sK0
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl10_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f417,plain,
    ( ~ r1_tarski(sK0,sK4(sK0))
    | ~ spl10_1
    | spl10_2
    | ~ spl10_3 ),
    inference(unit_resulting_resolution,[],[f243,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f243,plain,
    ( r2_hidden(sK4(sK0),sK0)
    | ~ spl10_1
    | spl10_2
    | ~ spl10_3 ),
    inference(unit_resulting_resolution,[],[f78,f242,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f242,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl10_1
    | spl10_2
    | ~ spl10_3 ),
    inference(unit_resulting_resolution,[],[f133,f239,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

fof(f239,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | ~ spl10_1
    | spl10_2
    | ~ spl10_3 ),
    inference(unit_resulting_resolution,[],[f125,f130,f133,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f130,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl10_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f125,plain,
    ( v1_funct_1(sK2)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl10_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f133,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl10_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f78,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f5,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f5,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f628,plain,
    ( ~ spl10_1
    | spl10_2
    | ~ spl10_3
    | spl10_4 ),
    inference(avatar_contradiction_clause,[],[f627])).

fof(f627,plain,
    ( $false
    | ~ spl10_1
    | spl10_2
    | ~ spl10_3
    | spl10_4 ),
    inference(subsumption_resolution,[],[f621,f501])).

fof(f501,plain,
    ( ~ m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(k2_relat_1(sK2)))
    | ~ spl10_1
    | spl10_2
    | ~ spl10_3
    | spl10_4 ),
    inference(unit_resulting_resolution,[],[f337,f479,f121])).

fof(f121,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | sP9(X1) ) ),
    inference(cnf_transformation,[],[f121_D])).

fof(f121_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ v1_xboole_0(X2)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) )
    <=> ~ sP9(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).

fof(f479,plain,
    ( ~ sP9(k2_relat_1(sK2))
    | spl10_4 ),
    inference(unit_resulting_resolution,[],[f279,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP9(X1) ) ),
    inference(general_splitting,[],[f109,f121_D])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f279,plain,
    ( r2_hidden(sK3(k2_relat_1(sK2)),k2_relat_1(sK2))
    | spl10_4 ),
    inference(unit_resulting_resolution,[],[f211,f77])).

fof(f77,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f211,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | spl10_4 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl10_4
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f337,plain,
    ( v1_xboole_0(k2_relat_1(sK2))
    | ~ spl10_1
    | spl10_2
    | ~ spl10_3 ),
    inference(unit_resulting_resolution,[],[f125,f239,f182,f177,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f177,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2)))) ),
    inference(forward_demodulation,[],[f172,f150])).

fof(f150,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f139,f138])).

fof(f138,plain,(
    sK2 = sK8(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f65,f118])).

fof(f118,plain,(
    ! [X6,X0,X1] :
      ( sK8(X0,X1,X6) = X6
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X6,X2,X0,X1] :
      ( sK8(X0,X1,X6) = X6
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X1)
                | k1_relat_1(X4) != X0
                | sK6(X0,X1,X2) != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( r1_tarski(k2_relat_1(sK7(X0,X1,X2)),X1)
              & k1_relat_1(sK7(X0,X1,X2)) = X0
              & sK6(X0,X1,X2) = sK7(X0,X1,X2)
              & v1_funct_1(sK7(X0,X1,X2))
              & v1_relat_1(sK7(X0,X1,X2)) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X1)
                  | k1_relat_1(X7) != X0
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ( r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X1)
                & k1_relat_1(sK8(X0,X1,X6)) = X0
                & sK8(X0,X1,X6) = X6
                & v1_funct_1(sK8(X0,X1,X6))
                & v1_relat_1(sK8(X0,X1,X6)) )
              | ~ r2_hidden(X6,X2) ) )
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f60,f63,f62,f61])).

fof(f61,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X1)
                | k1_relat_1(X4) != X0
                | X3 != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r1_tarski(k2_relat_1(X5),X1)
                & k1_relat_1(X5) = X0
                & X3 = X5
                & v1_funct_1(X5)
                & v1_relat_1(X5) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r1_tarski(k2_relat_1(X4),X1)
              | k1_relat_1(X4) != X0
              | sK6(X0,X1,X2) != X4
              | ~ v1_funct_1(X4)
              | ~ v1_relat_1(X4) )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r1_tarski(k2_relat_1(X5),X1)
              & k1_relat_1(X5) = X0
              & sK6(X0,X1,X2) = X5
              & v1_funct_1(X5)
              & v1_relat_1(X5) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(k2_relat_1(X5),X1)
          & k1_relat_1(X5) = X0
          & sK6(X0,X1,X2) = X5
          & v1_funct_1(X5)
          & v1_relat_1(X5) )
     => ( r1_tarski(k2_relat_1(sK7(X0,X1,X2)),X1)
        & k1_relat_1(sK7(X0,X1,X2)) = X0
        & sK6(X0,X1,X2) = sK7(X0,X1,X2)
        & v1_funct_1(sK7(X0,X1,X2))
        & v1_relat_1(sK7(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r1_tarski(k2_relat_1(X8),X1)
          & k1_relat_1(X8) = X0
          & X6 = X8
          & v1_funct_1(X8)
          & v1_relat_1(X8) )
     => ( r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X1)
        & k1_relat_1(sK8(X0,X1,X6)) = X0
        & sK8(X0,X1,X6) = X6
        & v1_funct_1(sK8(X0,X1,X6))
        & v1_relat_1(sK8(X0,X1,X6)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | k1_relat_1(X4) != X0
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X5] :
                  ( r1_tarski(k2_relat_1(X5),X1)
                  & k1_relat_1(X5) = X0
                  & X3 = X5
                  & v1_funct_1(X5)
                  & v1_relat_1(X5) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X1)
                  | k1_relat_1(X7) != X0
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ? [X8] :
                  ( r1_tarski(k2_relat_1(X8),X1)
                  & k1_relat_1(X8) = X0
                  & X6 = X8
                  & v1_funct_1(X8)
                  & v1_relat_1(X8) )
              | ~ r2_hidden(X6,X2) ) )
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | k1_relat_1(X4) != X0
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4] :
                  ( r1_tarski(k2_relat_1(X4),X1)
                  & k1_relat_1(X4) = X0
                  & X3 = X4
                  & v1_funct_1(X4)
                  & v1_relat_1(X4) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | k1_relat_1(X4) != X0
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) ) )
            & ( ? [X4] :
                  ( r1_tarski(k2_relat_1(X4),X1)
                  & k1_relat_1(X4) = X0
                  & X3 = X4
                  & v1_funct_1(X4)
                  & v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) ) )
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r1_tarski(k2_relat_1(X4),X1)
              & k1_relat_1(X4) = X0
              & X3 = X4
              & v1_funct_1(X4)
              & v1_relat_1(X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).

fof(f65,plain,(
    r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) )
    & r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f45])).

fof(f45,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
        & r2_hidden(X2,k1_funct_2(X0,X1)) )
   => ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
      & r2_hidden(sK2,k1_funct_2(sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

fof(f139,plain,(
    sK0 = k1_relat_1(sK8(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f65,f117])).

fof(f117,plain,(
    ! [X6,X0,X1] :
      ( k1_relat_1(sK8(X0,X1,X6)) = X0
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_relat_1(sK8(X0,X1,X6)) = X0
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f172,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    inference(unit_resulting_resolution,[],[f110,f110,f155,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f155,plain,(
    v1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f136,f138])).

fof(f136,plain,(
    v1_relat_1(sK8(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f65,f120])).

fof(f120,plain,(
    ! [X6,X0,X1] :
      ( v1_relat_1(sK8(X0,X1,X6))
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_relat_1(sK8(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f110,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f182,plain,
    ( v1_funct_2(sK2,sK0,k2_relat_1(sK2))
    | ~ spl10_1 ),
    inference(forward_demodulation,[],[f167,f150])).

fof(f167,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl10_1 ),
    inference(unit_resulting_resolution,[],[f125,f155,f75])).

fof(f75,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f621,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(k2_relat_1(sK2))) ),
    inference(backward_demodulation,[],[f610,f607])).

fof(f607,plain,(
    k2_relat_1(sK2) = k2_relat_1(k2_zfmisc_1(sK0,k2_relat_1(sK2))) ),
    inference(unit_resulting_resolution,[],[f80,f316,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f316,plain,(
    r1_tarski(k2_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK0,k2_relat_1(sK2)))) ),
    inference(unit_resulting_resolution,[],[f155,f79,f183,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f183,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,k2_relat_1(sK2))) ),
    inference(forward_demodulation,[],[f157,f150])).

fof(f157,plain,(
    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) ),
    inference(unit_resulting_resolution,[],[f155,f68])).

fof(f68,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f79,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f80,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t194_relat_1)).

fof(f610,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(k2_relat_1(k2_zfmisc_1(sK0,k2_relat_1(sK2))))) ),
    inference(unit_resulting_resolution,[],[f316,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f237,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f236,f132])).

fof(f236,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f229,f150])).

fof(f229,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
    inference(unit_resulting_resolution,[],[f155,f111,f151,f94])).

fof(f151,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(backward_demodulation,[],[f140,f138])).

fof(f140,plain,(
    r1_tarski(k2_relat_1(sK8(sK0,sK1,sK2)),sK1) ),
    inference(unit_resulting_resolution,[],[f65,f116])).

fof(f116,plain,(
    ! [X6,X0,X1] :
      ( r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X1)
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X1)
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f111,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f220,plain,
    ( ~ spl10_4
    | spl10_5 ),
    inference(avatar_split_clause,[],[f219,f213,f209])).

fof(f219,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f197,f155])).

fof(f197,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != k2_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f70,f150])).

fof(f70,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f156,plain,(
    spl10_1 ),
    inference(avatar_split_clause,[],[f152,f124])).

fof(f152,plain,(
    v1_funct_1(sK2) ),
    inference(forward_demodulation,[],[f137,f138])).

fof(f137,plain,(
    v1_funct_1(sK8(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f65,f119])).

fof(f119,plain,(
    ! [X6,X0,X1] :
      ( v1_funct_1(sK8(X0,X1,X6))
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_funct_1(sK8(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f135,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f66,f132,f128,f124])).

fof(f66,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:55:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.49  % (11805)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.49  % (11798)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.50  % (11808)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.50  % (11800)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (11804)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (11817)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (11817)Refutation not found, incomplete strategy% (11817)------------------------------
% 0.20/0.52  % (11817)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (11817)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (11817)Memory used [KB]: 10746
% 0.20/0.52  % (11817)Time elapsed: 0.108 s
% 0.20/0.52  % (11817)------------------------------
% 0.20/0.52  % (11817)------------------------------
% 0.20/0.52  % (11810)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (11799)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (11807)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (11826)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (11821)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (11816)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (11812)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (11819)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (11824)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.55  % (11819)Refutation not found, incomplete strategy% (11819)------------------------------
% 0.20/0.55  % (11819)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (11819)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (11819)Memory used [KB]: 10746
% 0.20/0.55  % (11819)Time elapsed: 0.105 s
% 0.20/0.55  % (11819)------------------------------
% 0.20/0.55  % (11819)------------------------------
% 0.20/0.55  % (11801)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.55  % (11802)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.56  % (11797)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.56  % (11806)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.57  % (11822)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.57  % (11823)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.57  % (11820)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.57  % (11809)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.57  % (11814)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.58  % (11803)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.58  % (11815)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.58  % (11818)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.58  % (11811)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.59  % (11813)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.75/0.59  % (11825)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.86/0.62  % (11823)Refutation found. Thanks to Tanya!
% 1.86/0.62  % SZS status Theorem for theBenchmark
% 1.86/0.62  % SZS output start Proof for theBenchmark
% 1.86/0.62  fof(f1008,plain,(
% 1.86/0.62    $false),
% 1.86/0.62    inference(avatar_sat_refutation,[],[f135,f156,f220,f237,f628,f948])).
% 1.86/0.62  fof(f948,plain,(
% 1.86/0.62    ~spl10_1 | spl10_2 | ~spl10_3 | ~spl10_5),
% 1.86/0.62    inference(avatar_contradiction_clause,[],[f947])).
% 1.86/0.62  fof(f947,plain,(
% 1.86/0.62    $false | (~spl10_1 | spl10_2 | ~spl10_3 | ~spl10_5)),
% 1.86/0.62    inference(subsumption_resolution,[],[f854,f67])).
% 1.86/0.62  fof(f67,plain,(
% 1.86/0.62    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.86/0.62    inference(cnf_transformation,[],[f4])).
% 1.86/0.62  fof(f4,axiom,(
% 1.86/0.62    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.86/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.86/0.62  fof(f854,plain,(
% 1.86/0.62    ~r1_tarski(k1_xboole_0,sK4(k1_xboole_0)) | (~spl10_1 | spl10_2 | ~spl10_3 | ~spl10_5)),
% 1.86/0.62    inference(backward_demodulation,[],[f417,f215])).
% 1.86/0.62  fof(f215,plain,(
% 1.86/0.62    k1_xboole_0 = sK0 | ~spl10_5),
% 1.86/0.62    inference(avatar_component_clause,[],[f213])).
% 1.86/0.62  fof(f213,plain,(
% 1.86/0.62    spl10_5 <=> k1_xboole_0 = sK0),
% 1.86/0.62    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 1.86/0.62  fof(f417,plain,(
% 1.86/0.62    ~r1_tarski(sK0,sK4(sK0)) | (~spl10_1 | spl10_2 | ~spl10_3)),
% 1.86/0.62    inference(unit_resulting_resolution,[],[f243,f93])).
% 1.86/0.62  fof(f93,plain,(
% 1.86/0.62    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.86/0.62    inference(cnf_transformation,[],[f39])).
% 1.86/0.62  fof(f39,plain,(
% 1.86/0.62    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.86/0.62    inference(ennf_transformation,[],[f15])).
% 1.86/0.62  fof(f15,axiom,(
% 1.86/0.62    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.86/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.86/0.62  fof(f243,plain,(
% 1.86/0.62    r2_hidden(sK4(sK0),sK0) | (~spl10_1 | spl10_2 | ~spl10_3)),
% 1.86/0.62    inference(unit_resulting_resolution,[],[f78,f242,f84])).
% 1.86/0.62  fof(f84,plain,(
% 1.86/0.62    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.86/0.62    inference(cnf_transformation,[],[f37])).
% 1.86/0.62  fof(f37,plain,(
% 1.86/0.62    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.86/0.62    inference(flattening,[],[f36])).
% 1.86/0.62  fof(f36,plain,(
% 1.86/0.62    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.86/0.62    inference(ennf_transformation,[],[f6])).
% 1.86/0.62  fof(f6,axiom,(
% 1.86/0.62    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.86/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 2.02/0.64  fof(f242,plain,(
% 2.02/0.64    ~v1_xboole_0(sK0) | (~spl10_1 | spl10_2 | ~spl10_3)),
% 2.02/0.64    inference(unit_resulting_resolution,[],[f133,f239,f83])).
% 2.02/0.64  fof(f83,plain,(
% 2.02/0.64    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 2.02/0.64    inference(cnf_transformation,[],[f35])).
% 2.02/0.64  fof(f35,plain,(
% 2.02/0.64    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 2.02/0.64    inference(ennf_transformation,[],[f18])).
% 2.02/0.64  fof(f18,axiom,(
% 2.02/0.64    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).
% 2.02/0.64  fof(f239,plain,(
% 2.02/0.64    ~v1_partfun1(sK2,sK0) | (~spl10_1 | spl10_2 | ~spl10_3)),
% 2.02/0.64    inference(unit_resulting_resolution,[],[f125,f130,f133,f96])).
% 2.02/0.64  fof(f96,plain,(
% 2.02/0.64    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.02/0.64    inference(cnf_transformation,[],[f43])).
% 2.02/0.64  fof(f43,plain,(
% 2.02/0.64    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.02/0.64    inference(flattening,[],[f42])).
% 2.02/0.64  fof(f42,plain,(
% 2.02/0.64    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.02/0.64    inference(ennf_transformation,[],[f17])).
% 2.02/0.64  fof(f17,axiom,(
% 2.02/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).
% 2.02/0.64  fof(f130,plain,(
% 2.02/0.64    ~v1_funct_2(sK2,sK0,sK1) | spl10_2),
% 2.02/0.64    inference(avatar_component_clause,[],[f128])).
% 2.02/0.64  fof(f128,plain,(
% 2.02/0.64    spl10_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 2.02/0.64    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 2.02/0.64  fof(f125,plain,(
% 2.02/0.64    v1_funct_1(sK2) | ~spl10_1),
% 2.02/0.64    inference(avatar_component_clause,[],[f124])).
% 2.02/0.64  fof(f124,plain,(
% 2.02/0.64    spl10_1 <=> v1_funct_1(sK2)),
% 2.02/0.64    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 2.02/0.64  fof(f133,plain,(
% 2.02/0.64    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl10_3),
% 2.02/0.64    inference(avatar_component_clause,[],[f132])).
% 2.02/0.64  fof(f132,plain,(
% 2.02/0.64    spl10_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.02/0.64    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 2.02/0.64  fof(f78,plain,(
% 2.02/0.64    ( ! [X0] : (m1_subset_1(sK4(X0),X0)) )),
% 2.02/0.64    inference(cnf_transformation,[],[f51])).
% 2.02/0.64  fof(f51,plain,(
% 2.02/0.64    ! [X0] : m1_subset_1(sK4(X0),X0)),
% 2.02/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f5,f50])).
% 2.02/0.64  fof(f50,plain,(
% 2.02/0.64    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK4(X0),X0))),
% 2.02/0.64    introduced(choice_axiom,[])).
% 2.02/0.64  fof(f5,axiom,(
% 2.02/0.64    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 2.02/0.64  fof(f628,plain,(
% 2.02/0.64    ~spl10_1 | spl10_2 | ~spl10_3 | spl10_4),
% 2.02/0.64    inference(avatar_contradiction_clause,[],[f627])).
% 2.02/0.64  fof(f627,plain,(
% 2.02/0.64    $false | (~spl10_1 | spl10_2 | ~spl10_3 | spl10_4)),
% 2.02/0.64    inference(subsumption_resolution,[],[f621,f501])).
% 2.02/0.64  fof(f501,plain,(
% 2.02/0.64    ~m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(k2_relat_1(sK2))) | (~spl10_1 | spl10_2 | ~spl10_3 | spl10_4)),
% 2.02/0.64    inference(unit_resulting_resolution,[],[f337,f479,f121])).
% 2.02/0.64  fof(f121,plain,(
% 2.02/0.64    ( ! [X2,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | sP9(X1)) )),
% 2.02/0.64    inference(cnf_transformation,[],[f121_D])).
% 2.02/0.64  fof(f121_D,plain,(
% 2.02/0.64    ( ! [X1] : (( ! [X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2))) ) <=> ~sP9(X1)) )),
% 2.02/0.64    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).
% 2.02/0.64  fof(f479,plain,(
% 2.02/0.64    ~sP9(k2_relat_1(sK2)) | spl10_4),
% 2.02/0.64    inference(unit_resulting_resolution,[],[f279,f122])).
% 2.02/0.64  fof(f122,plain,(
% 2.02/0.64    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~sP9(X1)) )),
% 2.02/0.64    inference(general_splitting,[],[f109,f121_D])).
% 2.02/0.64  fof(f109,plain,(
% 2.02/0.64    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.02/0.64    inference(cnf_transformation,[],[f44])).
% 2.02/0.64  fof(f44,plain,(
% 2.02/0.64    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.02/0.64    inference(ennf_transformation,[],[f8])).
% 2.02/0.64  fof(f8,axiom,(
% 2.02/0.64    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 2.02/0.64  fof(f279,plain,(
% 2.02/0.64    r2_hidden(sK3(k2_relat_1(sK2)),k2_relat_1(sK2)) | spl10_4),
% 2.02/0.64    inference(unit_resulting_resolution,[],[f211,f77])).
% 2.02/0.64  fof(f77,plain,(
% 2.02/0.64    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 2.02/0.64    inference(cnf_transformation,[],[f49])).
% 2.02/0.64  fof(f49,plain,(
% 2.02/0.64    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 2.02/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f48])).
% 2.02/0.64  fof(f48,plain,(
% 2.02/0.64    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 2.02/0.64    introduced(choice_axiom,[])).
% 2.02/0.64  fof(f32,plain,(
% 2.02/0.64    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.02/0.64    inference(ennf_transformation,[],[f2])).
% 2.02/0.64  fof(f2,axiom,(
% 2.02/0.64    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 2.02/0.64  fof(f211,plain,(
% 2.02/0.64    k1_xboole_0 != k2_relat_1(sK2) | spl10_4),
% 2.02/0.64    inference(avatar_component_clause,[],[f209])).
% 2.02/0.64  fof(f209,plain,(
% 2.02/0.64    spl10_4 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 2.02/0.64    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 2.02/0.64  fof(f337,plain,(
% 2.02/0.64    v1_xboole_0(k2_relat_1(sK2)) | (~spl10_1 | spl10_2 | ~spl10_3)),
% 2.02/0.64    inference(unit_resulting_resolution,[],[f125,f239,f182,f177,f82])).
% 2.02/0.64  fof(f82,plain,(
% 2.02/0.64    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.02/0.64    inference(cnf_transformation,[],[f34])).
% 2.02/0.64  fof(f34,plain,(
% 2.02/0.64    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.02/0.64    inference(flattening,[],[f33])).
% 2.02/0.64  fof(f33,plain,(
% 2.02/0.64    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.02/0.64    inference(ennf_transformation,[],[f19])).
% 2.02/0.64  fof(f19,axiom,(
% 2.02/0.64    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 2.02/0.64  fof(f177,plain,(
% 2.02/0.64    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2))))),
% 2.02/0.64    inference(forward_demodulation,[],[f172,f150])).
% 2.02/0.64  fof(f150,plain,(
% 2.02/0.64    sK0 = k1_relat_1(sK2)),
% 2.02/0.64    inference(backward_demodulation,[],[f139,f138])).
% 2.02/0.64  fof(f138,plain,(
% 2.02/0.64    sK2 = sK8(sK0,sK1,sK2)),
% 2.02/0.64    inference(unit_resulting_resolution,[],[f65,f118])).
% 2.02/0.64  fof(f118,plain,(
% 2.02/0.64    ( ! [X6,X0,X1] : (sK8(X0,X1,X6) = X6 | ~r2_hidden(X6,k1_funct_2(X0,X1))) )),
% 2.02/0.64    inference(equality_resolution,[],[f99])).
% 2.02/0.64  fof(f99,plain,(
% 2.02/0.64    ( ! [X6,X2,X0,X1] : (sK8(X0,X1,X6) = X6 | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 2.02/0.64    inference(cnf_transformation,[],[f64])).
% 2.02/0.64  fof(f64,plain,(
% 2.02/0.64    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | sK6(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r1_tarski(k2_relat_1(sK7(X0,X1,X2)),X1) & k1_relat_1(sK7(X0,X1,X2)) = X0 & sK6(X0,X1,X2) = sK7(X0,X1,X2) & v1_funct_1(sK7(X0,X1,X2)) & v1_relat_1(sK7(X0,X1,X2))) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X1) | k1_relat_1(X7) != X0 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & ((r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X1) & k1_relat_1(sK8(X0,X1,X6)) = X0 & sK8(X0,X1,X6) = X6 & v1_funct_1(sK8(X0,X1,X6)) & v1_relat_1(sK8(X0,X1,X6))) | ~r2_hidden(X6,X2))) | k1_funct_2(X0,X1) != X2))),
% 2.02/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f60,f63,f62,f61])).
% 2.02/0.64  fof(f61,plain,(
% 2.02/0.64    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X1) & k1_relat_1(X5) = X0 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2))) => ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | sK6(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X1) & k1_relat_1(X5) = X0 & sK6(X0,X1,X2) = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 2.02/0.64    introduced(choice_axiom,[])).
% 2.02/0.64  fof(f62,plain,(
% 2.02/0.64    ! [X2,X1,X0] : (? [X5] : (r1_tarski(k2_relat_1(X5),X1) & k1_relat_1(X5) = X0 & sK6(X0,X1,X2) = X5 & v1_funct_1(X5) & v1_relat_1(X5)) => (r1_tarski(k2_relat_1(sK7(X0,X1,X2)),X1) & k1_relat_1(sK7(X0,X1,X2)) = X0 & sK6(X0,X1,X2) = sK7(X0,X1,X2) & v1_funct_1(sK7(X0,X1,X2)) & v1_relat_1(sK7(X0,X1,X2))))),
% 2.02/0.64    introduced(choice_axiom,[])).
% 2.02/0.64  fof(f63,plain,(
% 2.02/0.64    ! [X6,X1,X0] : (? [X8] : (r1_tarski(k2_relat_1(X8),X1) & k1_relat_1(X8) = X0 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) => (r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X1) & k1_relat_1(sK8(X0,X1,X6)) = X0 & sK8(X0,X1,X6) = X6 & v1_funct_1(sK8(X0,X1,X6)) & v1_relat_1(sK8(X0,X1,X6))))),
% 2.02/0.64    introduced(choice_axiom,[])).
% 2.02/0.64  fof(f60,plain,(
% 2.02/0.64    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X1) & k1_relat_1(X5) = X0 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X1) | k1_relat_1(X7) != X0 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & (? [X8] : (r1_tarski(k2_relat_1(X8),X1) & k1_relat_1(X8) = X0 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) | ~r2_hidden(X6,X2))) | k1_funct_2(X0,X1) != X2))),
% 2.02/0.64    inference(rectify,[],[f59])).
% 2.02/0.64  fof(f59,plain,(
% 2.02/0.64    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4))) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | ~r2_hidden(X3,X2))) | k1_funct_2(X0,X1) != X2))),
% 2.02/0.64    inference(nnf_transformation,[],[f20])).
% 2.02/0.64  fof(f20,axiom,(
% 2.02/0.64    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).
% 2.02/0.64  fof(f65,plain,(
% 2.02/0.64    r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 2.02/0.64    inference(cnf_transformation,[],[f46])).
% 2.02/0.64  fof(f46,plain,(
% 2.02/0.64    (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) & r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 2.02/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f45])).
% 2.02/0.64  fof(f45,plain,(
% 2.02/0.64    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1))) => ((~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) & r2_hidden(sK2,k1_funct_2(sK0,sK1)))),
% 2.02/0.64    introduced(choice_axiom,[])).
% 2.02/0.64  fof(f24,plain,(
% 2.02/0.64    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1)))),
% 2.02/0.64    inference(ennf_transformation,[],[f23])).
% 2.02/0.64  fof(f23,negated_conjecture,(
% 2.02/0.64    ~! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.02/0.64    inference(negated_conjecture,[],[f22])).
% 2.02/0.64  fof(f22,conjecture,(
% 2.02/0.64    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).
% 2.02/0.64  fof(f139,plain,(
% 2.02/0.64    sK0 = k1_relat_1(sK8(sK0,sK1,sK2))),
% 2.02/0.64    inference(unit_resulting_resolution,[],[f65,f117])).
% 2.02/0.64  fof(f117,plain,(
% 2.02/0.64    ( ! [X6,X0,X1] : (k1_relat_1(sK8(X0,X1,X6)) = X0 | ~r2_hidden(X6,k1_funct_2(X0,X1))) )),
% 2.02/0.64    inference(equality_resolution,[],[f100])).
% 2.02/0.64  fof(f100,plain,(
% 2.02/0.64    ( ! [X6,X2,X0,X1] : (k1_relat_1(sK8(X0,X1,X6)) = X0 | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 2.02/0.64    inference(cnf_transformation,[],[f64])).
% 2.02/0.64  fof(f172,plain,(
% 2.02/0.64    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 2.02/0.64    inference(unit_resulting_resolution,[],[f110,f110,f155,f94])).
% 2.02/0.64  fof(f94,plain,(
% 2.02/0.64    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 2.02/0.64    inference(cnf_transformation,[],[f41])).
% 2.02/0.64  fof(f41,plain,(
% 2.02/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 2.02/0.64    inference(flattening,[],[f40])).
% 2.02/0.64  fof(f40,plain,(
% 2.02/0.64    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 2.02/0.64    inference(ennf_transformation,[],[f16])).
% 2.02/0.64  fof(f16,axiom,(
% 2.02/0.64    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 2.02/0.64  fof(f155,plain,(
% 2.02/0.64    v1_relat_1(sK2)),
% 2.02/0.64    inference(forward_demodulation,[],[f136,f138])).
% 2.02/0.64  fof(f136,plain,(
% 2.02/0.64    v1_relat_1(sK8(sK0,sK1,sK2))),
% 2.02/0.64    inference(unit_resulting_resolution,[],[f65,f120])).
% 2.02/0.64  fof(f120,plain,(
% 2.02/0.64    ( ! [X6,X0,X1] : (v1_relat_1(sK8(X0,X1,X6)) | ~r2_hidden(X6,k1_funct_2(X0,X1))) )),
% 2.02/0.64    inference(equality_resolution,[],[f97])).
% 2.02/0.64  fof(f97,plain,(
% 2.02/0.64    ( ! [X6,X2,X0,X1] : (v1_relat_1(sK8(X0,X1,X6)) | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 2.02/0.64    inference(cnf_transformation,[],[f64])).
% 2.02/0.64  fof(f110,plain,(
% 2.02/0.64    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.02/0.64    inference(equality_resolution,[],[f86])).
% 2.02/0.64  fof(f86,plain,(
% 2.02/0.64    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.02/0.64    inference(cnf_transformation,[],[f53])).
% 2.02/0.64  fof(f53,plain,(
% 2.02/0.64    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.02/0.64    inference(flattening,[],[f52])).
% 2.02/0.64  fof(f52,plain,(
% 2.02/0.64    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.02/0.64    inference(nnf_transformation,[],[f3])).
% 2.02/0.64  fof(f3,axiom,(
% 2.02/0.64    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.02/0.64  fof(f182,plain,(
% 2.02/0.64    v1_funct_2(sK2,sK0,k2_relat_1(sK2)) | ~spl10_1),
% 2.02/0.64    inference(forward_demodulation,[],[f167,f150])).
% 2.02/0.64  fof(f167,plain,(
% 2.02/0.64    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~spl10_1),
% 2.02/0.64    inference(unit_resulting_resolution,[],[f125,f155,f75])).
% 2.02/0.64  fof(f75,plain,(
% 2.02/0.64    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.02/0.64    inference(cnf_transformation,[],[f31])).
% 2.02/0.64  fof(f31,plain,(
% 2.02/0.64    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.02/0.64    inference(flattening,[],[f30])).
% 2.02/0.64  fof(f30,plain,(
% 2.02/0.64    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.02/0.64    inference(ennf_transformation,[],[f21])).
% 2.02/0.64  fof(f21,axiom,(
% 2.02/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 2.02/0.64  fof(f621,plain,(
% 2.02/0.64    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(k2_relat_1(sK2)))),
% 2.02/0.64    inference(backward_demodulation,[],[f610,f607])).
% 2.02/0.64  fof(f607,plain,(
% 2.02/0.64    k2_relat_1(sK2) = k2_relat_1(k2_zfmisc_1(sK0,k2_relat_1(sK2)))),
% 2.02/0.64    inference(unit_resulting_resolution,[],[f80,f316,f87])).
% 2.02/0.64  fof(f87,plain,(
% 2.02/0.64    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.02/0.64    inference(cnf_transformation,[],[f53])).
% 2.02/0.64  fof(f316,plain,(
% 2.02/0.64    r1_tarski(k2_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK0,k2_relat_1(sK2))))),
% 2.02/0.64    inference(unit_resulting_resolution,[],[f155,f79,f183,f72])).
% 2.02/0.64  fof(f72,plain,(
% 2.02/0.64    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.02/0.64    inference(cnf_transformation,[],[f28])).
% 2.02/0.64  fof(f28,plain,(
% 2.02/0.64    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.02/0.64    inference(flattening,[],[f27])).
% 2.02/0.64  fof(f27,plain,(
% 2.02/0.64    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.02/0.64    inference(ennf_transformation,[],[f13])).
% 2.02/0.64  fof(f13,axiom,(
% 2.02/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 2.02/0.64  fof(f183,plain,(
% 2.02/0.64    r1_tarski(sK2,k2_zfmisc_1(sK0,k2_relat_1(sK2)))),
% 2.02/0.64    inference(forward_demodulation,[],[f157,f150])).
% 2.02/0.64  fof(f157,plain,(
% 2.02/0.64    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))),
% 2.02/0.64    inference(unit_resulting_resolution,[],[f155,f68])).
% 2.02/0.64  fof(f68,plain,(
% 2.02/0.64    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 2.02/0.64    inference(cnf_transformation,[],[f25])).
% 2.02/0.64  fof(f25,plain,(
% 2.02/0.64    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.02/0.64    inference(ennf_transformation,[],[f12])).
% 2.02/0.64  fof(f12,axiom,(
% 2.02/0.64    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 2.02/0.64  fof(f79,plain,(
% 2.02/0.64    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.02/0.64    inference(cnf_transformation,[],[f10])).
% 2.02/0.64  fof(f10,axiom,(
% 2.02/0.64    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.02/0.64  fof(f80,plain,(
% 2.02/0.64    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)) )),
% 2.02/0.64    inference(cnf_transformation,[],[f11])).
% 2.02/0.64  fof(f11,axiom,(
% 2.02/0.64    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t194_relat_1)).
% 2.02/0.64  fof(f610,plain,(
% 2.02/0.64    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(k2_relat_1(k2_zfmisc_1(sK0,k2_relat_1(sK2)))))),
% 2.02/0.64    inference(unit_resulting_resolution,[],[f316,f92])).
% 2.02/0.64  fof(f92,plain,(
% 2.02/0.64    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.02/0.64    inference(cnf_transformation,[],[f58])).
% 2.02/0.64  fof(f58,plain,(
% 2.02/0.64    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.02/0.64    inference(nnf_transformation,[],[f7])).
% 2.02/0.64  fof(f7,axiom,(
% 2.02/0.64    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.02/0.64  fof(f237,plain,(
% 2.02/0.64    spl10_3),
% 2.02/0.64    inference(avatar_split_clause,[],[f236,f132])).
% 2.02/0.64  fof(f236,plain,(
% 2.02/0.64    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.02/0.64    inference(forward_demodulation,[],[f229,f150])).
% 2.02/0.64  fof(f229,plain,(
% 2.02/0.64    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))),
% 2.02/0.64    inference(unit_resulting_resolution,[],[f155,f111,f151,f94])).
% 2.02/0.64  fof(f151,plain,(
% 2.02/0.64    r1_tarski(k2_relat_1(sK2),sK1)),
% 2.02/0.64    inference(backward_demodulation,[],[f140,f138])).
% 2.02/0.64  fof(f140,plain,(
% 2.02/0.64    r1_tarski(k2_relat_1(sK8(sK0,sK1,sK2)),sK1)),
% 2.02/0.64    inference(unit_resulting_resolution,[],[f65,f116])).
% 2.02/0.64  fof(f116,plain,(
% 2.02/0.64    ( ! [X6,X0,X1] : (r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X1) | ~r2_hidden(X6,k1_funct_2(X0,X1))) )),
% 2.02/0.64    inference(equality_resolution,[],[f101])).
% 2.02/0.64  fof(f101,plain,(
% 2.02/0.64    ( ! [X6,X2,X0,X1] : (r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X1) | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 2.02/0.64    inference(cnf_transformation,[],[f64])).
% 2.02/0.64  fof(f111,plain,(
% 2.02/0.64    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.02/0.64    inference(equality_resolution,[],[f85])).
% 2.02/0.64  fof(f85,plain,(
% 2.02/0.64    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.02/0.64    inference(cnf_transformation,[],[f53])).
% 2.02/0.64  fof(f220,plain,(
% 2.02/0.64    ~spl10_4 | spl10_5),
% 2.02/0.64    inference(avatar_split_clause,[],[f219,f213,f209])).
% 2.02/0.64  fof(f219,plain,(
% 2.02/0.64    k1_xboole_0 = sK0 | k1_xboole_0 != k2_relat_1(sK2)),
% 2.02/0.64    inference(subsumption_resolution,[],[f197,f155])).
% 2.02/0.64  fof(f197,plain,(
% 2.02/0.64    k1_xboole_0 = sK0 | k1_xboole_0 != k2_relat_1(sK2) | ~v1_relat_1(sK2)),
% 2.02/0.64    inference(superposition,[],[f70,f150])).
% 2.02/0.64  fof(f70,plain,(
% 2.02/0.64    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.02/0.64    inference(cnf_transformation,[],[f47])).
% 2.02/0.64  fof(f47,plain,(
% 2.02/0.64    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.02/0.64    inference(nnf_transformation,[],[f26])).
% 2.02/0.64  fof(f26,plain,(
% 2.02/0.64    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.02/0.64    inference(ennf_transformation,[],[f14])).
% 2.02/0.64  fof(f14,axiom,(
% 2.02/0.64    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 2.02/0.64  fof(f156,plain,(
% 2.02/0.64    spl10_1),
% 2.02/0.64    inference(avatar_split_clause,[],[f152,f124])).
% 2.02/0.64  fof(f152,plain,(
% 2.02/0.64    v1_funct_1(sK2)),
% 2.02/0.64    inference(forward_demodulation,[],[f137,f138])).
% 2.02/0.64  fof(f137,plain,(
% 2.02/0.64    v1_funct_1(sK8(sK0,sK1,sK2))),
% 2.02/0.64    inference(unit_resulting_resolution,[],[f65,f119])).
% 2.02/0.64  fof(f119,plain,(
% 2.02/0.64    ( ! [X6,X0,X1] : (v1_funct_1(sK8(X0,X1,X6)) | ~r2_hidden(X6,k1_funct_2(X0,X1))) )),
% 2.02/0.64    inference(equality_resolution,[],[f98])).
% 2.02/0.64  fof(f98,plain,(
% 2.02/0.64    ( ! [X6,X2,X0,X1] : (v1_funct_1(sK8(X0,X1,X6)) | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 2.02/0.64    inference(cnf_transformation,[],[f64])).
% 2.02/0.64  fof(f135,plain,(
% 2.02/0.64    ~spl10_1 | ~spl10_2 | ~spl10_3),
% 2.02/0.64    inference(avatar_split_clause,[],[f66,f132,f128,f124])).
% 2.02/0.64  fof(f66,plain,(
% 2.02/0.64    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.02/0.64    inference(cnf_transformation,[],[f46])).
% 2.02/0.64  % SZS output end Proof for theBenchmark
% 2.02/0.64  % (11823)------------------------------
% 2.02/0.64  % (11823)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.02/0.64  % (11823)Termination reason: Refutation
% 2.02/0.64  
% 2.02/0.64  % (11823)Memory used [KB]: 11129
% 2.02/0.64  % (11823)Time elapsed: 0.198 s
% 2.02/0.64  % (11823)------------------------------
% 2.02/0.64  % (11823)------------------------------
% 2.02/0.64  % (11796)Success in time 0.277 s
%------------------------------------------------------------------------------
