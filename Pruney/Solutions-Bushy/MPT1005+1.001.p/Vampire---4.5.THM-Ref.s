%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1005+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 197 expanded)
%              Number of leaves         :   27 (  74 expanded)
%              Depth                    :   12
%              Number of atoms          :  381 ( 582 expanded)
%              Number of equality atoms :   69 ( 117 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f279,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f68,f72,f76,f81,f135,f156,f179,f182,f214,f254,f258])).

fof(f258,plain,
    ( spl7_11
    | ~ spl7_2
    | ~ spl7_5
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f163,f154,f79,f66,f113])).

fof(f113,plain,
    ( spl7_11
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f66,plain,
    ( spl7_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f79,plain,
    ( spl7_5
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f154,plain,
    ( spl7_13
  <=> o_0_0_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f163,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_2
    | ~ spl7_5
    | ~ spl7_13 ),
    inference(forward_demodulation,[],[f161,f80])).

fof(f80,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f161,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_2
    | ~ spl7_13 ),
    inference(resolution,[],[f160,f67])).

fof(f67,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f160,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X5)) )
    | ~ spl7_13 ),
    inference(superposition,[],[f125,f155])).

fof(f155,plain,
    ( o_0_0_xboole_0 = k1_relat_1(sK2)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f154])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f53,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f254,plain,
    ( ~ spl7_4
    | ~ spl7_5
    | ~ spl7_11
    | spl7_12
    | ~ spl7_18 ),
    inference(avatar_contradiction_clause,[],[f253])).

fof(f253,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_11
    | spl7_12
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f133,f250])).

fof(f250,plain,
    ( ! [X3] : o_0_0_xboole_0 = k9_relat_1(sK2,X3)
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_11
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f222,f117])).

fof(f117,plain,
    ( ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0)
    | ~ spl7_4
    | ~ spl7_11 ),
    inference(resolution,[],[f114,f92])).

fof(f92,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl7_4 ),
    inference(resolution,[],[f54,f75])).

fof(f75,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl7_4
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f114,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f113])).

fof(f222,plain,
    ( ! [X3] :
        ( r2_hidden(sK5(sK2,X3,sK6(k9_relat_1(sK2,X3))),o_0_0_xboole_0)
        | o_0_0_xboole_0 = k9_relat_1(sK2,X3) )
    | ~ spl7_5
    | ~ spl7_18 ),
    inference(forward_demodulation,[],[f220,f80])).

fof(f220,plain,
    ( ! [X3] :
        ( r2_hidden(sK5(sK2,X3,sK6(k9_relat_1(sK2,X3))),o_0_0_xboole_0)
        | k1_xboole_0 = k9_relat_1(sK2,X3) )
    | ~ spl7_18 ),
    inference(resolution,[],[f217,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f217,plain,
    ( ! [X0] :
        ( v1_xboole_0(k9_relat_1(sK2,X0))
        | r2_hidden(sK5(sK2,X0,sK6(k9_relat_1(sK2,X0))),o_0_0_xboole_0) )
    | ~ spl7_18 ),
    inference(resolution,[],[f215,f49])).

fof(f49,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f5,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f5,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f215,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k9_relat_1(sK2,X0))
        | v1_xboole_0(k9_relat_1(sK2,X0))
        | r2_hidden(sK5(sK2,X0,X1),o_0_0_xboole_0) )
    | ~ spl7_18 ),
    inference(resolution,[],[f213,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f213,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK2,X1))
        | r2_hidden(sK5(sK2,X1,X0),o_0_0_xboole_0) )
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl7_18
  <=> ! [X1,X0] :
        ( r2_hidden(sK5(sK2,X1,X0),o_0_0_xboole_0)
        | ~ r2_hidden(X0,k9_relat_1(sK2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f133,plain,
    ( o_0_0_xboole_0 != k9_relat_1(sK2,sK1)
    | spl7_12 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl7_12
  <=> o_0_0_xboole_0 = k9_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f214,plain,
    ( ~ spl7_14
    | spl7_18
    | ~ spl7_3
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f210,f154,f70,f212,f170])).

fof(f170,plain,
    ( spl7_14
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f70,plain,
    ( spl7_3
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f210,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK5(sK2,X1,X0),o_0_0_xboole_0)
        | ~ r2_hidden(X0,k9_relat_1(sK2,X1))
        | ~ v1_relat_1(sK2) )
    | ~ spl7_3
    | ~ spl7_13 ),
    inference(forward_demodulation,[],[f209,f155])).

fof(f209,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK2,X1))
        | r2_hidden(sK5(sK2,X1,X0),k1_relat_1(sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl7_3 ),
    inference(resolution,[],[f60,f71])).

fof(f71,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f60,plain,(
    ! [X6,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | r2_hidden(sK5(X0,X1,X6),k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

% (25613)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK3(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK3(X0,X1,X2),X2) )
              & ( ( sK3(X0,X1,X2) = k1_funct_1(X0,sK4(X0,X1,X2))
                  & r2_hidden(sK4(X0,X1,X2),X1)
                  & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK5(X0,X1,X6)) = X6
                    & r2_hidden(sK5(X0,X1,X6),X1)
                    & r2_hidden(sK5(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f29,f32,f31,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != X3
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( k1_funct_1(X0,X5) = X3
                & r2_hidden(X5,X1)
                & r2_hidden(X5,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( k1_funct_1(X0,X4) != sK3(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK3(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = sK3(X0,X1,X2)
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( sK3(X0,X1,X2) = k1_funct_1(X0,sK4(X0,X1,X2))
        & r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X1,X6)) = X6
        & r2_hidden(sK5(X0,X1,X6),X1)
        & r2_hidden(sK5(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( k1_funct_1(X0,X5) = X3
                      & r2_hidden(X5,X1)
                      & r2_hidden(X5,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ? [X8] :
                      ( k1_funct_1(X0,X8) = X6
                      & r2_hidden(X8,X1)
                      & r2_hidden(X8,k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

fof(f182,plain,
    ( spl7_7
    | ~ spl7_2
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f181,f79,f66,f89])).

fof(f89,plain,
    ( spl7_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f181,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK0)))
    | ~ spl7_2
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f67,f80])).

fof(f179,plain,
    ( ~ spl7_2
    | spl7_14 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | ~ spl7_2
    | spl7_14 ),
    inference(subsumption_resolution,[],[f67,f176])).

fof(f176,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl7_14 ),
    inference(resolution,[],[f171,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f171,plain,
    ( ~ v1_relat_1(sK2)
    | spl7_14 ),
    inference(avatar_component_clause,[],[f170])).

fof(f156,plain,
    ( spl7_13
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f151,f89,f79,f74,f154])).

fof(f151,plain,
    ( o_0_0_xboole_0 = k1_relat_1(sK2)
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_7 ),
    inference(resolution,[],[f148,f90])).

fof(f90,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK0)))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f89])).

fof(f148,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X5)))
        | o_0_0_xboole_0 = k1_relat_1(X4) )
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f147,f80])).

fof(f147,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X5)))
        | k1_xboole_0 = k1_relat_1(X4) )
    | ~ spl7_4 ),
    inference(resolution,[],[f145,f40])).

fof(f145,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(k1_relat_1(X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1))) )
    | ~ spl7_4 ),
    inference(resolution,[],[f137,f49])).

fof(f137,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_relat_1(X0))
        | v1_xboole_0(k1_relat_1(X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1))) )
    | ~ spl7_4 ),
    inference(resolution,[],[f126,f50])).

fof(f126,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k1_relat_1(X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1))) )
    | ~ spl7_4 ),
    inference(resolution,[],[f125,f92])).

fof(f135,plain,
    ( ~ spl7_12
    | ~ spl7_7
    | spl7_1
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f130,f79,f62,f89,f132])).

fof(f62,plain,
    ( spl7_1
  <=> k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f130,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK0)))
    | o_0_0_xboole_0 != k9_relat_1(sK2,sK1)
    | spl7_1
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f129,f80])).

fof(f129,plain,
    ( o_0_0_xboole_0 != k9_relat_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl7_1
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f127,f80])).

fof(f127,plain,
    ( k1_xboole_0 != k9_relat_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl7_1 ),
    inference(superposition,[],[f63,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f63,plain,
    ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f81,plain,
    ( spl7_5
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f77,f74,f79])).

fof(f77,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl7_4 ),
    inference(resolution,[],[f40,f75])).

fof(f76,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f39,f74])).

fof(f39,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f72,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f36,f70])).

fof(f36,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_1(X2) )
   => ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_1(X2) )
       => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_2)).

fof(f68,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f37,f66])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f64,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f38,f62])).

fof(f38,plain,(
    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f27])).

%------------------------------------------------------------------------------
