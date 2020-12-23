%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0643+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 286 expanded)
%              Number of leaves         :   31 ( 109 expanded)
%              Depth                    :   22
%              Number of atoms          :  748 (1716 expanded)
%              Number of equality atoms :  188 ( 571 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1448,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f93,f98,f103,f108,f113,f118,f123,f128,f133,f148,f193,f211,f232,f366,f1447])).

fof(f1447,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_11
    | ~ spl9_12
    | spl9_15
    | spl9_19
    | ~ spl9_26 ),
    inference(avatar_contradiction_clause,[],[f1446])).

fof(f1446,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_11
    | ~ spl9_12
    | spl9_15
    | spl9_19
    | ~ spl9_26 ),
    inference(subsumption_resolution,[],[f1445,f231])).

fof(f231,plain,
    ( sK8(sK0,sK2) != k1_funct_1(sK2,sK8(sK0,sK2))
    | spl9_19 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl9_19
  <=> sK8(sK0,sK2) = k1_funct_1(sK2,sK8(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f1445,plain,
    ( sK8(sK0,sK2) = k1_funct_1(sK2,sK8(sK0,sK2))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_11
    | ~ spl9_12
    | spl9_15
    | ~ spl9_26 ),
    inference(subsumption_resolution,[],[f1439,f192])).

fof(f192,plain,
    ( r2_hidden(sK8(sK0,sK2),sK0)
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl9_12
  <=> r2_hidden(sK8(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f1439,plain,
    ( ~ r2_hidden(sK8(sK0,sK2),sK0)
    | sK8(sK0,sK2) = k1_funct_1(sK2,sK8(sK0,sK2))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_11
    | ~ spl9_12
    | spl9_15
    | ~ spl9_26 ),
    inference(equality_resolution,[],[f690])).

fof(f690,plain,
    ( ! [X2] :
        ( k1_funct_1(sK1,sK8(sK0,sK2)) != k1_funct_1(sK1,X2)
        | ~ r2_hidden(X2,sK0)
        | k1_funct_1(sK2,sK8(sK0,sK2)) = X2 )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_11
    | ~ spl9_12
    | spl9_15
    | ~ spl9_26 ),
    inference(subsumption_resolution,[],[f426,f679])).

fof(f679,plain,
    ( r2_hidden(k1_funct_1(sK2,sK8(sK0,sK2)),sK0)
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_11
    | ~ spl9_12
    | spl9_15 ),
    inference(unit_resulting_resolution,[],[f192,f667])).

fof(f667,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK2,X0),sK0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_11
    | spl9_15 ),
    inference(forward_demodulation,[],[f666,f117])).

fof(f117,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl9_7
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f666,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | r2_hidden(k1_funct_1(sK2,X0),sK0) )
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_11
    | spl9_15 ),
    inference(subsumption_resolution,[],[f665,f210])).

fof(f210,plain,
    ( ~ v1_xboole_0(sK0)
    | spl9_15 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl9_15
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f665,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | v1_xboole_0(sK0)
        | r2_hidden(k1_funct_1(sK2,X0),sK0) )
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f664,f102])).

fof(f102,plain,
    ( v1_funct_1(sK2)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl9_4
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f664,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK2)
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | v1_xboole_0(sK0)
        | r2_hidden(k1_funct_1(sK2,X0),sK0) )
    | ~ spl9_3
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f662,f97])).

fof(f97,plain,
    ( v1_relat_1(sK2)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl9_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f662,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2)
        | ~ v1_funct_1(sK2)
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | v1_xboole_0(sK0)
        | r2_hidden(k1_funct_1(sK2,X0),sK0) )
    | ~ spl9_11 ),
    inference(resolution,[],[f294,f147])).

fof(f147,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl9_11
  <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f294,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X1))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | v1_xboole_0(X1)
      | r2_hidden(k1_funct_1(X0,X2),X1) ) ),
    inference(resolution,[],[f149,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_funct_1(X1,X0),X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X1)) ) ),
    inference(resolution,[],[f77,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f77,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK5(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK5(X0,X1),X1) )
              & ( ( sK5(X0,X1) = k1_funct_1(X0,sK6(X0,X1))
                  & r2_hidden(sK6(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK5(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK7(X0,X5)) = X5
                    & r2_hidden(sK7(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f36,f39,f38,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK5(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK5(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK5(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK5(X0,X1) = k1_funct_1(X0,sK6(X0,X1))
        & r2_hidden(sK6(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK7(X0,X5)) = X5
        & r2_hidden(sK7(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

% (19567)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f426,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK0)
        | ~ r2_hidden(k1_funct_1(sK2,sK8(sK0,sK2)),sK0)
        | k1_funct_1(sK1,sK8(sK0,sK2)) != k1_funct_1(sK1,X2)
        | k1_funct_1(sK2,sK8(sK0,sK2)) = X2 )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_26 ),
    inference(forward_demodulation,[],[f425,f112])).

fof(f112,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl9_6
  <=> sK0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f425,plain,
    ( ! [X2] :
        ( ~ r2_hidden(k1_funct_1(sK2,sK8(sK0,sK2)),sK0)
        | k1_funct_1(sK1,sK8(sK0,sK2)) != k1_funct_1(sK1,X2)
        | k1_funct_1(sK2,sK8(sK0,sK2)) = X2
        | ~ r2_hidden(X2,k1_relat_1(sK1)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_26 ),
    inference(forward_demodulation,[],[f424,f112])).

fof(f424,plain,
    ( ! [X2] :
        ( k1_funct_1(sK1,sK8(sK0,sK2)) != k1_funct_1(sK1,X2)
        | k1_funct_1(sK2,sK8(sK0,sK2)) = X2
        | ~ r2_hidden(k1_funct_1(sK2,sK8(sK0,sK2)),k1_relat_1(sK1))
        | ~ r2_hidden(X2,k1_relat_1(sK1)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_26 ),
    inference(subsumption_resolution,[],[f423,f87])).

fof(f87,plain,
    ( v1_relat_1(sK1)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl9_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f423,plain,
    ( ! [X2] :
        ( k1_funct_1(sK1,sK8(sK0,sK2)) != k1_funct_1(sK1,X2)
        | k1_funct_1(sK2,sK8(sK0,sK2)) = X2
        | ~ r2_hidden(k1_funct_1(sK2,sK8(sK0,sK2)),k1_relat_1(sK1))
        | ~ r2_hidden(X2,k1_relat_1(sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_26 ),
    inference(subsumption_resolution,[],[f422,f92])).

fof(f92,plain,
    ( v1_funct_1(sK1)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl9_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f422,plain,
    ( ! [X2] :
        ( k1_funct_1(sK1,sK8(sK0,sK2)) != k1_funct_1(sK1,X2)
        | k1_funct_1(sK2,sK8(sK0,sK2)) = X2
        | ~ r2_hidden(k1_funct_1(sK2,sK8(sK0,sK2)),k1_relat_1(sK1))
        | ~ r2_hidden(X2,k1_relat_1(sK1))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl9_5
    | ~ spl9_26 ),
    inference(subsumption_resolution,[],[f413,f107])).

fof(f107,plain,
    ( v2_funct_1(sK1)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl9_5
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f413,plain,
    ( ! [X2] :
        ( k1_funct_1(sK1,sK8(sK0,sK2)) != k1_funct_1(sK1,X2)
        | k1_funct_1(sK2,sK8(sK0,sK2)) = X2
        | ~ r2_hidden(k1_funct_1(sK2,sK8(sK0,sK2)),k1_relat_1(sK1))
        | ~ r2_hidden(X2,k1_relat_1(sK1))
        | ~ v2_funct_1(sK1)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl9_26 ),
    inference(superposition,[],[f56,f365])).

fof(f365,plain,
    ( k1_funct_1(sK1,sK8(sK0,sK2)) = k1_funct_1(sK1,k1_funct_1(sK2,sK8(sK0,sK2)))
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f363])).

fof(f363,plain,
    ( spl9_26
  <=> k1_funct_1(sK1,sK8(sK0,sK2)) = k1_funct_1(sK1,k1_funct_1(sK2,sK8(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f56,plain,(
    ! [X4,X0,X3] :
      ( k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | X3 = X4
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK3(X0) != sK4(X0)
            & k1_funct_1(X0,sK3(X0)) = k1_funct_1(X0,sK4(X0))
            & r2_hidden(sK4(X0),k1_relat_1(X0))
            & r2_hidden(sK3(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f32,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK3(X0) != sK4(X0)
        & k1_funct_1(X0,sK3(X0)) = k1_funct_1(X0,sK4(X0))
        & r2_hidden(sK4(X0),k1_relat_1(X0))
        & r2_hidden(sK3(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

fof(f366,plain,
    ( spl9_26
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_10
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f273,f190,f130,f115,f100,f95,f90,f85,f363])).

fof(f130,plain,
    ( spl9_10
  <=> sK1 = k5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f273,plain,
    ( k1_funct_1(sK1,sK8(sK0,sK2)) = k1_funct_1(sK1,k1_funct_1(sK2,sK8(sK0,sK2)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_10
    | ~ spl9_12 ),
    inference(forward_demodulation,[],[f263,f132])).

fof(f132,plain,
    ( sK1 = k5_relat_1(sK2,sK1)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f130])).

fof(f263,plain,
    ( k1_funct_1(sK1,k1_funct_1(sK2,sK8(sK0,sK2))) = k1_funct_1(k5_relat_1(sK2,sK1),sK8(sK0,sK2))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_12 ),
    inference(unit_resulting_resolution,[],[f92,f87,f192,f186])).

fof(f186,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_1(X3)
        | ~ r2_hidden(X2,sK0)
        | ~ v1_relat_1(X3)
        | k1_funct_1(k5_relat_1(sK2,X3),X2) = k1_funct_1(X3,k1_funct_1(sK2,X2)) )
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7 ),
    inference(forward_demodulation,[],[f185,f117])).

fof(f185,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k1_relat_1(sK2))
        | ~ v1_funct_1(X3)
        | ~ v1_relat_1(X3)
        | k1_funct_1(k5_relat_1(sK2,X3),X2) = k1_funct_1(X3,k1_funct_1(sK2,X2)) )
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f182,f97])).

fof(f182,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k1_relat_1(sK2))
        | ~ v1_funct_1(X3)
        | ~ v1_relat_1(X3)
        | k1_funct_1(k5_relat_1(sK2,X3),X2) = k1_funct_1(X3,k1_funct_1(sK2,X2))
        | ~ v1_relat_1(sK2) )
    | ~ spl9_4 ),
    inference(resolution,[],[f72,f102])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

fof(f232,plain,
    ( ~ spl9_19
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7
    | spl9_9 ),
    inference(avatar_split_clause,[],[f175,f125,f115,f100,f95,f229])).

fof(f125,plain,
    ( spl9_9
  <=> k6_relat_1(sK0) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f175,plain,
    ( sK8(sK0,sK2) != k1_funct_1(sK2,sK8(sK0,sK2))
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7
    | spl9_9 ),
    inference(subsumption_resolution,[],[f174,f97])).

fof(f174,plain,
    ( sK8(sK0,sK2) != k1_funct_1(sK2,sK8(sK0,sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl9_4
    | ~ spl9_7
    | spl9_9 ),
    inference(subsumption_resolution,[],[f173,f102])).

fof(f173,plain,
    ( sK8(sK0,sK2) != k1_funct_1(sK2,sK8(sK0,sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl9_7
    | spl9_9 ),
    inference(subsumption_resolution,[],[f170,f127])).

fof(f127,plain,
    ( k6_relat_1(sK0) != sK2
    | spl9_9 ),
    inference(avatar_component_clause,[],[f125])).

fof(f170,plain,
    ( sK8(sK0,sK2) != k1_funct_1(sK2,sK8(sK0,sK2))
    | k6_relat_1(sK0) = sK2
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl9_7 ),
    inference(superposition,[],[f80,f117])).

fof(f80,plain,(
    ! [X1] :
      ( sK8(k1_relat_1(X1),X1) != k1_funct_1(X1,sK8(k1_relat_1(X1),X1))
      | k6_relat_1(k1_relat_1(X1)) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | sK8(X0,X1) != k1_funct_1(X1,sK8(X0,X1))
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( sK8(X0,X1) != k1_funct_1(X1,sK8(X0,X1))
            & r2_hidden(sK8(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f43,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( sK8(X0,X1) != k1_funct_1(X1,sK8(X0,X1))
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

fof(f211,plain,
    ( ~ spl9_15
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f194,f190,f208])).

fof(f194,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl9_12 ),
    inference(unit_resulting_resolution,[],[f192,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f193,plain,
    ( spl9_12
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7
    | spl9_9 ),
    inference(avatar_split_clause,[],[f162,f125,f115,f100,f95,f190])).

fof(f162,plain,
    ( r2_hidden(sK8(sK0,sK2),sK0)
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7
    | spl9_9 ),
    inference(subsumption_resolution,[],[f161,f127])).

fof(f161,plain,
    ( k6_relat_1(sK0) = sK2
    | r2_hidden(sK8(sK0,sK2),sK0)
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7 ),
    inference(forward_demodulation,[],[f160,f117])).

fof(f160,plain,
    ( r2_hidden(sK8(sK0,sK2),sK0)
    | sK2 = k6_relat_1(k1_relat_1(sK2))
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7 ),
    inference(forward_demodulation,[],[f159,f117])).

fof(f159,plain,
    ( r2_hidden(sK8(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
    | sK2 = k6_relat_1(k1_relat_1(sK2))
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f155,f97])).

fof(f155,plain,
    ( r2_hidden(sK8(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
    | sK2 = k6_relat_1(k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl9_4 ),
    inference(resolution,[],[f81,f102])).

fof(f81,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | r2_hidden(sK8(k1_relat_1(X1),X1),k1_relat_1(X1))
      | k6_relat_1(k1_relat_1(X1)) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | r2_hidden(sK8(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f148,plain,
    ( spl9_11
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f134,f120,f145])).

fof(f120,plain,
    ( spl9_8
  <=> r1_tarski(k2_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f134,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl9_8 ),
    inference(unit_resulting_resolution,[],[f122,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f122,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f120])).

fof(f133,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f54,f130])).

fof(f54,plain,(
    sK1 = k5_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( k6_relat_1(sK0) != sK2
    & sK1 = k5_relat_1(sK2,sK1)
    & v2_funct_1(sK1)
    & r1_tarski(k2_relat_1(sK2),sK0)
    & sK0 = k1_relat_1(sK2)
    & sK0 = k1_relat_1(sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f29,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k6_relat_1(X0) != X2
            & k5_relat_1(X2,X1) = X1
            & v2_funct_1(X1)
            & r1_tarski(k2_relat_1(X2),X0)
            & k1_relat_1(X2) = X0
            & k1_relat_1(X1) = X0
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k6_relat_1(sK0) != X2
          & sK1 = k5_relat_1(X2,sK1)
          & v2_funct_1(sK1)
          & r1_tarski(k2_relat_1(X2),sK0)
          & k1_relat_1(X2) = sK0
          & sK0 = k1_relat_1(sK1)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( k6_relat_1(sK0) != X2
        & sK1 = k5_relat_1(X2,sK1)
        & v2_funct_1(sK1)
        & r1_tarski(k2_relat_1(X2),sK0)
        & k1_relat_1(X2) = sK0
        & sK0 = k1_relat_1(sK1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k6_relat_1(sK0) != sK2
      & sK1 = k5_relat_1(sK2,sK1)
      & v2_funct_1(sK1)
      & r1_tarski(k2_relat_1(sK2),sK0)
      & sK0 = k1_relat_1(sK2)
      & sK0 = k1_relat_1(sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k6_relat_1(X0) != X2
          & k5_relat_1(X2,X1) = X1
          & v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X0
          & k1_relat_1(X1) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k6_relat_1(X0) != X2
          & k5_relat_1(X2,X1) = X1
          & v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X0
          & k1_relat_1(X1) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( ( k5_relat_1(X2,X1) = X1
                & v2_funct_1(X1)
                & r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X0
                & k1_relat_1(X1) = X0 )
             => k6_relat_1(X0) = X2 ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( ( k5_relat_1(X2,X1) = X1
              & v2_funct_1(X1)
              & r1_tarski(k2_relat_1(X2),X0)
              & k1_relat_1(X2) = X0
              & k1_relat_1(X1) = X0 )
           => k6_relat_1(X0) = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_1)).

fof(f128,plain,(
    ~ spl9_9 ),
    inference(avatar_split_clause,[],[f55,f125])).

fof(f55,plain,(
    k6_relat_1(sK0) != sK2 ),
    inference(cnf_transformation,[],[f30])).

fof(f123,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f52,f120])).

fof(f52,plain,(
    r1_tarski(k2_relat_1(sK2),sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f118,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f51,f115])).

fof(f51,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f113,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f50,f110])).

fof(f50,plain,(
    sK0 = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f108,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f53,f105])).

fof(f53,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f103,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f49,f100])).

fof(f49,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f98,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f48,f95])).

fof(f48,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f93,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f47,f90])).

fof(f47,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f88,plain,(
    spl9_1 ),
    inference(avatar_split_clause,[],[f46,f85])).

fof(f46,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

%------------------------------------------------------------------------------
