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
% DateTime   : Thu Dec  3 12:58:00 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 296 expanded)
%              Number of leaves         :   36 ( 123 expanded)
%              Depth                    :   13
%              Number of atoms          :  556 (1141 expanded)
%              Number of equality atoms :   33 (  71 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1292,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f70,f75,f86,f93,f111,f134,f142,f147,f152,f196,f262,f286,f293,f294,f311,f312,f321,f324,f717,f742,f1244,f1257,f1266,f1291])).

fof(f1291,plain,
    ( ~ spl7_13
    | ~ spl7_30
    | ~ spl7_66
    | spl7_70 ),
    inference(avatar_contradiction_clause,[],[f1290])).

fof(f1290,plain,
    ( $false
    | ~ spl7_13
    | ~ spl7_30
    | ~ spl7_66
    | spl7_70 ),
    inference(subsumption_resolution,[],[f1252,f740])).

fof(f740,plain,
    ( ~ r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2)))
    | spl7_70 ),
    inference(avatar_component_clause,[],[f739])).

fof(f739,plain,
    ( spl7_70
  <=> r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).

fof(f1252,plain,
    ( r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2)))
    | ~ spl7_13
    | ~ spl7_30
    | ~ spl7_66 ),
    inference(forward_demodulation,[],[f1246,f310])).

fof(f310,plain,
    ( k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2)) = k11_relat_1(sK2,sK3(sK0,sK0,sK1,sK2))
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f308])).

fof(f308,plain,
    ( spl7_30
  <=> k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2)) = k11_relat_1(sK2,sK3(sK0,sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f1246,plain,
    ( r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK2,sK3(sK0,sK0,sK1,sK2)))
    | ~ spl7_13
    | ~ spl7_66 ),
    inference(resolution,[],[f712,f146])).

fof(f146,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(X1,k11_relat_1(sK2,X0)) )
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl7_13
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(X1,k11_relat_1(sK2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f712,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK2)
    | ~ spl7_66 ),
    inference(avatar_component_clause,[],[f710])).

fof(f710,plain,
    ( spl7_66
  <=> r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).

fof(f1266,plain,
    ( ~ spl7_4
    | spl7_67
    | ~ spl7_70 ),
    inference(avatar_contradiction_clause,[],[f1263])).

fof(f1263,plain,
    ( $false
    | ~ spl7_4
    | spl7_67
    | ~ spl7_70 ),
    inference(unit_resulting_resolution,[],[f85,f741,f715,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(f715,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1)
    | spl7_67 ),
    inference(avatar_component_clause,[],[f714])).

fof(f714,plain,
    ( spl7_67
  <=> r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_67])])).

fof(f741,plain,
    ( r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2)))
    | ~ spl7_70 ),
    inference(avatar_component_clause,[],[f739])).

fof(f85,plain,
    ( v1_relat_1(sK1)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl7_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f1257,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_66
    | ~ spl7_67 ),
    inference(avatar_contradiction_clause,[],[f1256])).

fof(f1256,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_66
    | ~ spl7_67 ),
    inference(subsumption_resolution,[],[f1255,f69])).

fof(f69,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl7_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f1255,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl7_1
    | ~ spl7_3
    | ~ spl7_66
    | ~ spl7_67 ),
    inference(subsumption_resolution,[],[f1254,f74])).

fof(f74,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl7_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f1254,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl7_1
    | ~ spl7_66
    | ~ spl7_67 ),
    inference(subsumption_resolution,[],[f1253,f716])).

fof(f716,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1)
    | ~ spl7_67 ),
    inference(avatar_component_clause,[],[f714])).

fof(f1253,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl7_1
    | ~ spl7_66 ),
    inference(subsumption_resolution,[],[f1249,f64])).

fof(f64,plain,
    ( ~ r2_relset_1(sK0,sK0,sK1,sK2)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl7_1
  <=> r2_relset_1(sK0,sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f1249,plain,
    ( r2_relset_1(sK0,sK0,sK1,sK2)
    | ~ r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_66 ),
    inference(resolution,[],[f712,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X3)
      | r2_relset_1(X0,X1,X2,X3)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_relset_1(X0,X1,X2,X3)
              | ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X3)
                  | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X2) )
                & ( r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X3)
                  | r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X2) )
                & m1_subset_1(sK4(X0,X1,X2,X3),X1)
                & m1_subset_1(sK3(X0,X1,X2,X3),X0) ) )
            & ( ! [X6] :
                  ( ! [X7] :
                      ( ( ( r2_hidden(k4_tarski(X6,X7),X2)
                          | ~ r2_hidden(k4_tarski(X6,X7),X3) )
                        & ( r2_hidden(k4_tarski(X6,X7),X3)
                          | ~ r2_hidden(k4_tarski(X6,X7),X2) ) )
                      | ~ m1_subset_1(X7,X1) )
                  | ~ m1_subset_1(X6,X0) )
              | ~ r2_relset_1(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f28,f30,f29])).

fof(f29,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ? [X5] :
              ( ( ~ r2_hidden(k4_tarski(X4,X5),X3)
                | ~ r2_hidden(k4_tarski(X4,X5),X2) )
              & ( r2_hidden(k4_tarski(X4,X5),X3)
                | r2_hidden(k4_tarski(X4,X5),X2) )
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,X0) )
     => ( ? [X5] :
            ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),X5),X3)
              | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),X5),X2) )
            & ( r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),X5),X3)
              | r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),X5),X2) )
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK3(X0,X1,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),X5),X3)
            | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),X5),X2) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),X5),X3)
            | r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),X5),X2) )
          & m1_subset_1(X5,X1) )
     => ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X3)
          | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X2) )
        & ( r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X3)
          | r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X2) )
        & m1_subset_1(sK4(X0,X1,X2,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_relset_1(X0,X1,X2,X3)
              | ? [X4] :
                  ( ? [X5] :
                      ( ( ~ r2_hidden(k4_tarski(X4,X5),X3)
                        | ~ r2_hidden(k4_tarski(X4,X5),X2) )
                      & ( r2_hidden(k4_tarski(X4,X5),X3)
                        | r2_hidden(k4_tarski(X4,X5),X2) )
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X6] :
                  ( ! [X7] :
                      ( ( ( r2_hidden(k4_tarski(X6,X7),X2)
                          | ~ r2_hidden(k4_tarski(X6,X7),X3) )
                        & ( r2_hidden(k4_tarski(X6,X7),X3)
                          | ~ r2_hidden(k4_tarski(X6,X7),X2) ) )
                      | ~ m1_subset_1(X7,X1) )
                  | ~ m1_subset_1(X6,X0) )
              | ~ r2_relset_1(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_relset_1(X0,X1,X2,X3)
              | ? [X4] :
                  ( ? [X5] :
                      ( ( ~ r2_hidden(k4_tarski(X4,X5),X3)
                        | ~ r2_hidden(k4_tarski(X4,X5),X2) )
                      & ( r2_hidden(k4_tarski(X4,X5),X3)
                        | r2_hidden(k4_tarski(X4,X5),X2) )
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( ( ( r2_hidden(k4_tarski(X4,X5),X2)
                          | ~ r2_hidden(k4_tarski(X4,X5),X3) )
                        & ( r2_hidden(k4_tarski(X4,X5),X3)
                          | ~ r2_hidden(k4_tarski(X4,X5),X2) ) )
                      | ~ m1_subset_1(X5,X1) )
                  | ~ m1_subset_1(X4,X0) )
              | ~ r2_relset_1(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_relset_1(X0,X1,X2,X3)
              | ? [X4] :
                  ( ? [X5] :
                      ( ( ~ r2_hidden(k4_tarski(X4,X5),X3)
                        | ~ r2_hidden(k4_tarski(X4,X5),X2) )
                      & ( r2_hidden(k4_tarski(X4,X5),X3)
                        | r2_hidden(k4_tarski(X4,X5),X2) )
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( ( ( r2_hidden(k4_tarski(X4,X5),X2)
                          | ~ r2_hidden(k4_tarski(X4,X5),X3) )
                        & ( r2_hidden(k4_tarski(X4,X5),X3)
                          | ~ r2_hidden(k4_tarski(X4,X5),X2) ) )
                      | ~ m1_subset_1(X5,X1) )
                  | ~ m1_subset_1(X4,X0) )
              | ~ r2_relset_1(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r2_relset_1(X0,X1,X2,X3)
          <=> ! [X4] :
                ( ! [X5] :
                    ( ( r2_hidden(k4_tarski(X4,X5),X2)
                    <=> r2_hidden(k4_tarski(X4,X5),X3) )
                    | ~ m1_subset_1(X5,X1) )
                | ~ m1_subset_1(X4,X0) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( r2_relset_1(X0,X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,X0)
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r2_hidden(k4_tarski(X4,X5),X2)
                    <=> r2_hidden(k4_tarski(X4,X5),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relset_1)).

fof(f1244,plain,
    ( spl7_66
    | ~ spl7_31
    | ~ spl7_70 ),
    inference(avatar_split_clause,[],[f1238,f739,f319,f710])).

fof(f319,plain,
    ( spl7_31
  <=> ! [X1] :
        ( ~ r2_hidden(X1,k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2)))
        | r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),X1),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f1238,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK2)
    | ~ spl7_31
    | ~ spl7_70 ),
    inference(resolution,[],[f320,f741])).

fof(f320,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2)))
        | r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),X1),sK2) )
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f319])).

fof(f742,plain,
    ( spl7_70
    | ~ spl7_10
    | ~ spl7_67 ),
    inference(avatar_split_clause,[],[f718,f714,f132,f739])).

fof(f132,plain,
    ( spl7_10
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | r2_hidden(X1,k11_relat_1(sK1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f718,plain,
    ( r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2)))
    | ~ spl7_10
    | ~ spl7_67 ),
    inference(resolution,[],[f716,f133])).

fof(f133,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | r2_hidden(X1,k11_relat_1(sK1,X0)) )
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f132])).

fof(f717,plain,
    ( spl7_66
    | spl7_67
    | spl7_1
    | ~ spl7_3
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f631,f280,f72,f62,f714,f710])).

fof(f280,plain,
    ( spl7_27
  <=> ! [X0] :
        ( r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,X0),sK4(sK0,sK0,sK1,X0)),X0)
        | r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,X0),sK4(sK0,sK0,sK1,X0)),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | r2_relset_1(sK0,sK0,sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f631,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1)
    | r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK2)
    | spl7_1
    | ~ spl7_3
    | ~ spl7_27 ),
    inference(subsumption_resolution,[],[f623,f64])).

fof(f623,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1)
    | r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK2)
    | r2_relset_1(sK0,sK0,sK1,sK2)
    | ~ spl7_3
    | ~ spl7_27 ),
    inference(resolution,[],[f74,f281])).

fof(f281,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,X0),sK4(sK0,sK0,sK1,X0)),sK1)
        | r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,X0),sK4(sK0,sK0,sK1,X0)),X0)
        | r2_relset_1(sK0,sK0,sK1,X0) )
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f280])).

fof(f324,plain,
    ( k1_xboole_0 != sK2
    | r2_relset_1(sK0,sK0,k1_xboole_0,sK2)
    | ~ r2_relset_1(sK0,sK0,sK2,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f321,plain,
    ( spl7_31
    | ~ spl7_5
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f316,f308,f90,f319])).

fof(f90,plain,
    ( spl7_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f316,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2)))
        | r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),X1),sK2) )
    | ~ spl7_5
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f314,f92])).

fof(f92,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f90])).

fof(f314,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2)))
        | r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),X1),sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_30 ),
    inference(superposition,[],[f46,f310])).

fof(f312,plain,
    ( spl7_27
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f220,f67,f280])).

fof(f220,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,X0),sK4(sK0,sK0,sK1,X0)),X0)
        | r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,X0),sK4(sK0,sK0,sK1,X0)),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | r2_relset_1(sK0,sK0,sK1,X0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f69,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X3)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f311,plain,
    ( spl7_30
    | spl7_1
    | ~ spl7_3
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f305,f284,f72,f62,f308])).

fof(f284,plain,
    ( spl7_28
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | r2_relset_1(sK0,sK0,sK1,X0)
        | k11_relat_1(sK1,sK3(sK0,sK0,sK1,X0)) = k11_relat_1(sK2,sK3(sK0,sK0,sK1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f305,plain,
    ( k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2)) = k11_relat_1(sK2,sK3(sK0,sK0,sK1,sK2))
    | spl7_1
    | ~ spl7_3
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f304,f64])).

fof(f304,plain,
    ( r2_relset_1(sK0,sK0,sK1,sK2)
    | k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2)) = k11_relat_1(sK2,sK3(sK0,sK0,sK1,sK2))
    | ~ spl7_3
    | ~ spl7_28 ),
    inference(resolution,[],[f285,f74])).

fof(f285,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | r2_relset_1(sK0,sK0,sK1,X0)
        | k11_relat_1(sK1,sK3(sK0,sK0,sK1,X0)) = k11_relat_1(sK2,sK3(sK0,sK0,sK1,X0)) )
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f284])).

fof(f294,plain,
    ( ~ spl7_3
    | ~ spl7_11
    | spl7_24 ),
    inference(avatar_contradiction_clause,[],[f288])).

fof(f288,plain,
    ( $false
    | ~ spl7_3
    | ~ spl7_11
    | spl7_24 ),
    inference(unit_resulting_resolution,[],[f236,f74,f138,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f138,plain,
    ( v1_xboole_0(sK0)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl7_11
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f236,plain,
    ( ~ v1_xboole_0(sK2)
    | spl7_24 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl7_24
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f293,plain,
    ( ~ spl7_2
    | ~ spl7_11
    | spl7_16 ),
    inference(avatar_contradiction_clause,[],[f287])).

fof(f287,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_11
    | spl7_16 ),
    inference(unit_resulting_resolution,[],[f160,f69,f138,f44])).

fof(f160,plain,
    ( ~ v1_xboole_0(sK1)
    | spl7_16 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl7_16
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f286,plain,
    ( spl7_28
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f228,f150,f140,f284])).

fof(f140,plain,
    ( spl7_12
  <=> ! [X0] :
        ( k11_relat_1(sK1,X0) = k11_relat_1(sK2,X0)
        | ~ m1_subset_1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f150,plain,
    ( spl7_14
  <=> ! [X0] :
        ( m1_subset_1(sK3(sK0,sK0,sK1,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | r2_relset_1(sK0,sK0,sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f228,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | r2_relset_1(sK0,sK0,sK1,X0)
        | k11_relat_1(sK1,sK3(sK0,sK0,sK1,X0)) = k11_relat_1(sK2,sK3(sK0,sK0,sK1,X0)) )
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(resolution,[],[f151,f141])).

fof(f141,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | k11_relat_1(sK1,X0) = k11_relat_1(sK2,X0) )
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f140])).

fof(f151,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3(sK0,sK0,sK1,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | r2_relset_1(sK0,sK0,sK1,X0) )
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f150])).

fof(f262,plain,
    ( spl7_26
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f245,f235,f259])).

fof(f259,plain,
    ( spl7_26
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f245,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_24 ),
    inference(resolution,[],[f237,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f237,plain,
    ( v1_xboole_0(sK2)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f235])).

fof(f196,plain,
    ( ~ spl7_21
    | spl7_1
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f179,f159,f62,f193])).

fof(f193,plain,
    ( spl7_21
  <=> r2_relset_1(sK0,sK0,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f179,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_xboole_0,sK2)
    | spl7_1
    | ~ spl7_16 ),
    inference(backward_demodulation,[],[f64,f173])).

fof(f173,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_16 ),
    inference(resolution,[],[f161,f38])).

fof(f161,plain,
    ( v1_xboole_0(sK1)
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f159])).

fof(f152,plain,
    ( spl7_14
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f114,f67,f150])).

fof(f114,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3(sK0,sK0,sK1,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | r2_relset_1(sK0,sK0,sK1,X0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f49,f69])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(sK3(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f147,plain,
    ( spl7_13
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f98,f90,f145])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(X1,k11_relat_1(sK2,X0)) )
    | ~ spl7_5 ),
    inference(resolution,[],[f92,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k11_relat_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f142,plain,
    ( spl7_11
    | spl7_12 ),
    inference(avatar_split_clause,[],[f79,f140,f136])).

fof(f79,plain,(
    ! [X0] :
      ( k11_relat_1(sK1,X0) = k11_relat_1(sK2,X0)
      | ~ m1_subset_1(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f35,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f35,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK0)
      | k11_relat_1(sK1,X3) = k11_relat_1(sK2,X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r2_relset_1(sK0,sK0,sK1,sK2)
    & ! [X3] :
        ( k11_relat_1(sK1,X3) = k11_relat_1(sK2,X3)
        | ~ r2_hidden(X3,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f22,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X1,X2)
            & ! [X3] :
                ( k11_relat_1(X1,X3) = k11_relat_1(X2,X3)
                | ~ r2_hidden(X3,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK0,sK0,sK1,X2)
          & ! [X3] :
              ( k11_relat_1(X2,X3) = k11_relat_1(sK1,X3)
              | ~ r2_hidden(X3,sK0) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2] :
        ( ~ r2_relset_1(sK0,sK0,sK1,X2)
        & ! [X3] :
            ( k11_relat_1(X2,X3) = k11_relat_1(sK1,X3)
            | ~ r2_hidden(X3,sK0) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
   => ( ~ r2_relset_1(sK0,sK0,sK1,sK2)
      & ! [X3] :
          ( k11_relat_1(sK1,X3) = k11_relat_1(sK2,X3)
          | ~ r2_hidden(X3,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X1,X2)
          & ! [X3] :
              ( k11_relat_1(X1,X3) = k11_relat_1(X2,X3)
              | ~ r2_hidden(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X1,X2)
          & ! [X3] :
              ( k11_relat_1(X1,X3) = k11_relat_1(X2,X3)
              | ~ r2_hidden(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
           => ( ! [X3] :
                  ( r2_hidden(X3,X0)
                 => k11_relat_1(X1,X3) = k11_relat_1(X2,X3) )
             => r2_relset_1(X0,X0,X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
         => ( ! [X3] :
                ( r2_hidden(X3,X0)
               => k11_relat_1(X1,X3) = k11_relat_1(X2,X3) )
           => r2_relset_1(X0,X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relset_1)).

fof(f134,plain,
    ( spl7_10
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f95,f83,f132])).

fof(f95,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | r2_hidden(X1,k11_relat_1(sK1,X0)) )
    | ~ spl7_4 ),
    inference(resolution,[],[f85,f45])).

fof(f111,plain,
    ( spl7_7
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f88,f72,f108])).

fof(f108,plain,
    ( spl7_7
  <=> r2_relset_1(sK0,sK0,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f88,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ spl7_3 ),
    inference(resolution,[],[f60,f74])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f93,plain,
    ( spl7_5
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f81,f72,f90])).

fof(f81,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_3 ),
    inference(resolution,[],[f76,f74])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f37,f39])).

fof(f39,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f86,plain,
    ( spl7_4
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f80,f67,f83])).

fof(f80,plain,
    ( v1_relat_1(sK1)
    | ~ spl7_2 ),
    inference(resolution,[],[f76,f69])).

fof(f75,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f34,f72])).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f70,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f33,f67])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f65,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f36,f62])).

fof(f36,plain,(
    ~ r2_relset_1(sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n016.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 16:53:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.45  % (20863)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.18/0.46  % (20872)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.18/0.46  % (20863)Refutation not found, incomplete strategy% (20863)------------------------------
% 0.18/0.46  % (20863)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.46  % (20863)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.46  
% 0.18/0.46  % (20863)Memory used [KB]: 1663
% 0.18/0.46  % (20863)Time elapsed: 0.056 s
% 0.18/0.46  % (20863)------------------------------
% 0.18/0.46  % (20863)------------------------------
% 0.18/0.46  % (20860)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.18/0.47  % (20858)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.18/0.47  % (20859)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.18/0.47  % (20871)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.18/0.48  % (20869)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.18/0.48  % (20866)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.18/0.48  % (20867)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.18/0.49  % (20873)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.18/0.49  % (20877)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.18/0.49  % (20864)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.18/0.49  % (20861)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.18/0.49  % (20876)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.18/0.50  % (20878)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.18/0.50  % (20882)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.18/0.50  % (20880)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.18/0.51  % (20875)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.30/0.51  % (20870)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.30/0.51  % (20879)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.30/0.51  % (20856)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.30/0.52  % (20856)Refutation not found, incomplete strategy% (20856)------------------------------
% 1.30/0.52  % (20856)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.52  % (20856)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.52  
% 1.30/0.52  % (20856)Memory used [KB]: 10618
% 1.30/0.52  % (20856)Time elapsed: 0.114 s
% 1.30/0.52  % (20856)------------------------------
% 1.30/0.52  % (20856)------------------------------
% 1.30/0.52  % (20862)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.30/0.52  % (20857)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.44/0.53  % (20874)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.44/0.54  % (20865)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.44/0.55  % (20881)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.44/0.55  % (20858)Refutation found. Thanks to Tanya!
% 1.44/0.55  % SZS status Theorem for theBenchmark
% 1.44/0.55  % SZS output start Proof for theBenchmark
% 1.44/0.55  fof(f1292,plain,(
% 1.44/0.55    $false),
% 1.44/0.55    inference(avatar_sat_refutation,[],[f65,f70,f75,f86,f93,f111,f134,f142,f147,f152,f196,f262,f286,f293,f294,f311,f312,f321,f324,f717,f742,f1244,f1257,f1266,f1291])).
% 1.44/0.56  fof(f1291,plain,(
% 1.44/0.56    ~spl7_13 | ~spl7_30 | ~spl7_66 | spl7_70),
% 1.44/0.56    inference(avatar_contradiction_clause,[],[f1290])).
% 1.44/0.56  fof(f1290,plain,(
% 1.44/0.56    $false | (~spl7_13 | ~spl7_30 | ~spl7_66 | spl7_70)),
% 1.44/0.56    inference(subsumption_resolution,[],[f1252,f740])).
% 1.44/0.56  fof(f740,plain,(
% 1.44/0.56    ~r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2))) | spl7_70),
% 1.44/0.56    inference(avatar_component_clause,[],[f739])).
% 1.44/0.56  fof(f739,plain,(
% 1.44/0.56    spl7_70 <=> r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2)))),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).
% 1.44/0.56  fof(f1252,plain,(
% 1.44/0.56    r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2))) | (~spl7_13 | ~spl7_30 | ~spl7_66)),
% 1.44/0.56    inference(forward_demodulation,[],[f1246,f310])).
% 1.44/0.56  fof(f310,plain,(
% 1.44/0.56    k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2)) = k11_relat_1(sK2,sK3(sK0,sK0,sK1,sK2)) | ~spl7_30),
% 1.44/0.56    inference(avatar_component_clause,[],[f308])).
% 1.44/0.56  fof(f308,plain,(
% 1.44/0.56    spl7_30 <=> k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2)) = k11_relat_1(sK2,sK3(sK0,sK0,sK1,sK2))),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 1.44/0.56  fof(f1246,plain,(
% 1.44/0.56    r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK2,sK3(sK0,sK0,sK1,sK2))) | (~spl7_13 | ~spl7_66)),
% 1.44/0.56    inference(resolution,[],[f712,f146])).
% 1.44/0.56  fof(f146,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | r2_hidden(X1,k11_relat_1(sK2,X0))) ) | ~spl7_13),
% 1.44/0.56    inference(avatar_component_clause,[],[f145])).
% 1.44/0.56  fof(f145,plain,(
% 1.44/0.56    spl7_13 <=> ! [X1,X0] : (~r2_hidden(k4_tarski(X0,X1),sK2) | r2_hidden(X1,k11_relat_1(sK2,X0)))),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 1.44/0.56  fof(f712,plain,(
% 1.44/0.56    r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK2) | ~spl7_66),
% 1.44/0.56    inference(avatar_component_clause,[],[f710])).
% 1.44/0.56  fof(f710,plain,(
% 1.44/0.56    spl7_66 <=> r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK2)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).
% 1.44/0.56  fof(f1266,plain,(
% 1.44/0.56    ~spl7_4 | spl7_67 | ~spl7_70),
% 1.44/0.56    inference(avatar_contradiction_clause,[],[f1263])).
% 1.44/0.56  fof(f1263,plain,(
% 1.44/0.56    $false | (~spl7_4 | spl7_67 | ~spl7_70)),
% 1.44/0.56    inference(unit_resulting_resolution,[],[f85,f741,f715,f46])).
% 1.44/0.56  fof(f46,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f25])).
% 1.44/0.56  fof(f25,plain,(
% 1.44/0.56    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 1.44/0.56    inference(nnf_transformation,[],[f17])).
% 1.44/0.56  fof(f17,plain,(
% 1.44/0.56    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 1.44/0.56    inference(ennf_transformation,[],[f5])).
% 1.44/0.56  fof(f5,axiom,(
% 1.44/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).
% 1.44/0.56  fof(f715,plain,(
% 1.44/0.56    ~r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1) | spl7_67),
% 1.44/0.56    inference(avatar_component_clause,[],[f714])).
% 1.44/0.56  fof(f714,plain,(
% 1.44/0.56    spl7_67 <=> r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_67])])).
% 1.44/0.56  fof(f741,plain,(
% 1.44/0.56    r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2))) | ~spl7_70),
% 1.44/0.56    inference(avatar_component_clause,[],[f739])).
% 1.44/0.56  fof(f85,plain,(
% 1.44/0.56    v1_relat_1(sK1) | ~spl7_4),
% 1.44/0.56    inference(avatar_component_clause,[],[f83])).
% 1.44/0.56  fof(f83,plain,(
% 1.44/0.56    spl7_4 <=> v1_relat_1(sK1)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.44/0.56  fof(f1257,plain,(
% 1.44/0.56    spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_66 | ~spl7_67),
% 1.44/0.56    inference(avatar_contradiction_clause,[],[f1256])).
% 1.44/0.56  fof(f1256,plain,(
% 1.44/0.56    $false | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_66 | ~spl7_67)),
% 1.44/0.56    inference(subsumption_resolution,[],[f1255,f69])).
% 1.44/0.56  fof(f69,plain,(
% 1.44/0.56    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl7_2),
% 1.44/0.56    inference(avatar_component_clause,[],[f67])).
% 1.44/0.56  fof(f67,plain,(
% 1.44/0.56    spl7_2 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.44/0.56  fof(f1255,plain,(
% 1.44/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (spl7_1 | ~spl7_3 | ~spl7_66 | ~spl7_67)),
% 1.44/0.56    inference(subsumption_resolution,[],[f1254,f74])).
% 1.44/0.56  fof(f74,plain,(
% 1.44/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl7_3),
% 1.44/0.56    inference(avatar_component_clause,[],[f72])).
% 1.44/0.56  fof(f72,plain,(
% 1.44/0.56    spl7_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.44/0.56  fof(f1254,plain,(
% 1.44/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (spl7_1 | ~spl7_66 | ~spl7_67)),
% 1.44/0.56    inference(subsumption_resolution,[],[f1253,f716])).
% 1.44/0.56  fof(f716,plain,(
% 1.44/0.56    r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1) | ~spl7_67),
% 1.44/0.56    inference(avatar_component_clause,[],[f714])).
% 1.44/0.56  fof(f1253,plain,(
% 1.44/0.56    ~r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (spl7_1 | ~spl7_66)),
% 1.44/0.56    inference(subsumption_resolution,[],[f1249,f64])).
% 1.44/0.56  fof(f64,plain,(
% 1.44/0.56    ~r2_relset_1(sK0,sK0,sK1,sK2) | spl7_1),
% 1.44/0.56    inference(avatar_component_clause,[],[f62])).
% 1.44/0.56  fof(f62,plain,(
% 1.44/0.56    spl7_1 <=> r2_relset_1(sK0,sK0,sK1,sK2)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.44/0.56  fof(f1249,plain,(
% 1.44/0.56    r2_relset_1(sK0,sK0,sK1,sK2) | ~r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl7_66),
% 1.44/0.56    inference(resolution,[],[f712,f52])).
% 1.44/0.56  fof(f52,plain,(
% 1.44/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X3) | r2_relset_1(X0,X1,X2,X3) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.44/0.56    inference(cnf_transformation,[],[f31])).
% 1.44/0.56  fof(f31,plain,(
% 1.44/0.56    ! [X0,X1,X2] : (! [X3] : (((r2_relset_1(X0,X1,X2,X3) | (((~r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X3) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X2)) & (r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X3) | r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X2)) & m1_subset_1(sK4(X0,X1,X2,X3),X1)) & m1_subset_1(sK3(X0,X1,X2,X3),X0))) & (! [X6] : (! [X7] : (((r2_hidden(k4_tarski(X6,X7),X2) | ~r2_hidden(k4_tarski(X6,X7),X3)) & (r2_hidden(k4_tarski(X6,X7),X3) | ~r2_hidden(k4_tarski(X6,X7),X2))) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f28,f30,f29])).
% 1.44/0.56  fof(f29,plain,(
% 1.44/0.56    ! [X3,X2,X1,X0] : (? [X4] : (? [X5] : ((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) => (? [X5] : ((~r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),X5),X3) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),X5),X2)) & (r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),X5),X3) | r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),X5),X2)) & m1_subset_1(X5,X1)) & m1_subset_1(sK3(X0,X1,X2,X3),X0)))),
% 1.44/0.56    introduced(choice_axiom,[])).
% 1.44/0.56  fof(f30,plain,(
% 1.44/0.56    ! [X3,X2,X1,X0] : (? [X5] : ((~r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),X5),X3) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),X5),X2)) & (r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),X5),X3) | r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),X5),X2)) & m1_subset_1(X5,X1)) => ((~r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X3) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X2)) & (r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X3) | r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X2)) & m1_subset_1(sK4(X0,X1,X2,X3),X1)))),
% 1.44/0.56    introduced(choice_axiom,[])).
% 1.44/0.56  fof(f28,plain,(
% 1.44/0.56    ! [X0,X1,X2] : (! [X3] : (((r2_relset_1(X0,X1,X2,X3) | ? [X4] : (? [X5] : ((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0))) & (! [X6] : (! [X7] : (((r2_hidden(k4_tarski(X6,X7),X2) | ~r2_hidden(k4_tarski(X6,X7),X3)) & (r2_hidden(k4_tarski(X6,X7),X3) | ~r2_hidden(k4_tarski(X6,X7),X2))) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.56    inference(rectify,[],[f27])).
% 1.44/0.56  fof(f27,plain,(
% 1.44/0.56    ! [X0,X1,X2] : (! [X3] : (((r2_relset_1(X0,X1,X2,X3) | ? [X4] : (? [X5] : ((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0))) & (! [X4] : (! [X5] : (((r2_hidden(k4_tarski(X4,X5),X2) | ~r2_hidden(k4_tarski(X4,X5),X3)) & (r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2))) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0)) | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.56    inference(flattening,[],[f26])).
% 1.44/0.56  fof(f26,plain,(
% 1.44/0.56    ! [X0,X1,X2] : (! [X3] : (((r2_relset_1(X0,X1,X2,X3) | ? [X4] : (? [X5] : (((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2))) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0))) & (! [X4] : (! [X5] : (((r2_hidden(k4_tarski(X4,X5),X2) | ~r2_hidden(k4_tarski(X4,X5),X3)) & (r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2))) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0)) | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.56    inference(nnf_transformation,[],[f18])).
% 1.44/0.56  fof(f18,plain,(
% 1.44/0.56    ! [X0,X1,X2] : (! [X3] : ((r2_relset_1(X0,X1,X2,X3) <=> ! [X4] : (! [X5] : ((r2_hidden(k4_tarski(X4,X5),X2) <=> r2_hidden(k4_tarski(X4,X5),X3)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.56    inference(ennf_transformation,[],[f7])).
% 1.44/0.56  fof(f7,axiom,(
% 1.44/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,X2,X3) <=> ! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => (r2_hidden(k4_tarski(X4,X5),X2) <=> r2_hidden(k4_tarski(X4,X5),X3)))))))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relset_1)).
% 1.44/0.56  fof(f1244,plain,(
% 1.44/0.56    spl7_66 | ~spl7_31 | ~spl7_70),
% 1.44/0.56    inference(avatar_split_clause,[],[f1238,f739,f319,f710])).
% 1.44/0.56  fof(f319,plain,(
% 1.44/0.56    spl7_31 <=> ! [X1] : (~r2_hidden(X1,k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2))) | r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),X1),sK2))),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 1.44/0.56  fof(f1238,plain,(
% 1.44/0.56    r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK2) | (~spl7_31 | ~spl7_70)),
% 1.44/0.56    inference(resolution,[],[f320,f741])).
% 1.44/0.56  fof(f320,plain,(
% 1.44/0.56    ( ! [X1] : (~r2_hidden(X1,k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2))) | r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),X1),sK2)) ) | ~spl7_31),
% 1.44/0.56    inference(avatar_component_clause,[],[f319])).
% 1.44/0.56  fof(f742,plain,(
% 1.44/0.56    spl7_70 | ~spl7_10 | ~spl7_67),
% 1.44/0.56    inference(avatar_split_clause,[],[f718,f714,f132,f739])).
% 1.44/0.56  fof(f132,plain,(
% 1.44/0.56    spl7_10 <=> ! [X1,X0] : (~r2_hidden(k4_tarski(X0,X1),sK1) | r2_hidden(X1,k11_relat_1(sK1,X0)))),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.44/0.56  fof(f718,plain,(
% 1.44/0.56    r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2))) | (~spl7_10 | ~spl7_67)),
% 1.44/0.56    inference(resolution,[],[f716,f133])).
% 1.44/0.56  fof(f133,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | r2_hidden(X1,k11_relat_1(sK1,X0))) ) | ~spl7_10),
% 1.44/0.56    inference(avatar_component_clause,[],[f132])).
% 1.44/0.56  fof(f717,plain,(
% 1.44/0.56    spl7_66 | spl7_67 | spl7_1 | ~spl7_3 | ~spl7_27),
% 1.44/0.56    inference(avatar_split_clause,[],[f631,f280,f72,f62,f714,f710])).
% 1.44/0.56  fof(f280,plain,(
% 1.44/0.56    spl7_27 <=> ! [X0] : (r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,X0),sK4(sK0,sK0,sK1,X0)),X0) | r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,X0),sK4(sK0,sK0,sK1,X0)),sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | r2_relset_1(sK0,sK0,sK1,X0))),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 1.44/0.56  fof(f631,plain,(
% 1.44/0.56    r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1) | r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK2) | (spl7_1 | ~spl7_3 | ~spl7_27)),
% 1.44/0.56    inference(subsumption_resolution,[],[f623,f64])).
% 1.44/0.56  fof(f623,plain,(
% 1.44/0.56    r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1) | r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK2) | r2_relset_1(sK0,sK0,sK1,sK2) | (~spl7_3 | ~spl7_27)),
% 1.44/0.56    inference(resolution,[],[f74,f281])).
% 1.44/0.56  fof(f281,plain,(
% 1.44/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,X0),sK4(sK0,sK0,sK1,X0)),sK1) | r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,X0),sK4(sK0,sK0,sK1,X0)),X0) | r2_relset_1(sK0,sK0,sK1,X0)) ) | ~spl7_27),
% 1.44/0.56    inference(avatar_component_clause,[],[f280])).
% 1.44/0.56  fof(f324,plain,(
% 1.44/0.56    k1_xboole_0 != sK2 | r2_relset_1(sK0,sK0,k1_xboole_0,sK2) | ~r2_relset_1(sK0,sK0,sK2,sK2)),
% 1.44/0.56    introduced(theory_tautology_sat_conflict,[])).
% 1.44/0.56  fof(f321,plain,(
% 1.44/0.56    spl7_31 | ~spl7_5 | ~spl7_30),
% 1.44/0.56    inference(avatar_split_clause,[],[f316,f308,f90,f319])).
% 1.44/0.56  fof(f90,plain,(
% 1.44/0.56    spl7_5 <=> v1_relat_1(sK2)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.44/0.56  fof(f316,plain,(
% 1.44/0.56    ( ! [X1] : (~r2_hidden(X1,k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2))) | r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),X1),sK2)) ) | (~spl7_5 | ~spl7_30)),
% 1.44/0.56    inference(subsumption_resolution,[],[f314,f92])).
% 1.44/0.56  fof(f92,plain,(
% 1.44/0.56    v1_relat_1(sK2) | ~spl7_5),
% 1.44/0.56    inference(avatar_component_clause,[],[f90])).
% 1.44/0.56  fof(f314,plain,(
% 1.44/0.56    ( ! [X1] : (~r2_hidden(X1,k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2))) | r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),X1),sK2) | ~v1_relat_1(sK2)) ) | ~spl7_30),
% 1.44/0.56    inference(superposition,[],[f46,f310])).
% 1.44/0.56  fof(f312,plain,(
% 1.44/0.56    spl7_27 | ~spl7_2),
% 1.44/0.56    inference(avatar_split_clause,[],[f220,f67,f280])).
% 1.44/0.56  fof(f220,plain,(
% 1.44/0.56    ( ! [X0] : (r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,X0),sK4(sK0,sK0,sK1,X0)),X0) | r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,X0),sK4(sK0,sK0,sK1,X0)),sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | r2_relset_1(sK0,sK0,sK1,X0)) ) | ~spl7_2),
% 1.44/0.56    inference(resolution,[],[f69,f51])).
% 1.44/0.56  fof(f51,plain,(
% 1.44/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X3) | r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X3)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f31])).
% 1.44/0.56  fof(f311,plain,(
% 1.44/0.56    spl7_30 | spl7_1 | ~spl7_3 | ~spl7_28),
% 1.44/0.56    inference(avatar_split_clause,[],[f305,f284,f72,f62,f308])).
% 1.44/0.56  fof(f284,plain,(
% 1.44/0.56    spl7_28 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | r2_relset_1(sK0,sK0,sK1,X0) | k11_relat_1(sK1,sK3(sK0,sK0,sK1,X0)) = k11_relat_1(sK2,sK3(sK0,sK0,sK1,X0)))),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 1.44/0.56  fof(f305,plain,(
% 1.44/0.56    k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2)) = k11_relat_1(sK2,sK3(sK0,sK0,sK1,sK2)) | (spl7_1 | ~spl7_3 | ~spl7_28)),
% 1.44/0.56    inference(subsumption_resolution,[],[f304,f64])).
% 1.44/0.56  fof(f304,plain,(
% 1.44/0.56    r2_relset_1(sK0,sK0,sK1,sK2) | k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2)) = k11_relat_1(sK2,sK3(sK0,sK0,sK1,sK2)) | (~spl7_3 | ~spl7_28)),
% 1.44/0.56    inference(resolution,[],[f285,f74])).
% 1.44/0.56  fof(f285,plain,(
% 1.44/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | r2_relset_1(sK0,sK0,sK1,X0) | k11_relat_1(sK1,sK3(sK0,sK0,sK1,X0)) = k11_relat_1(sK2,sK3(sK0,sK0,sK1,X0))) ) | ~spl7_28),
% 1.44/0.56    inference(avatar_component_clause,[],[f284])).
% 1.44/0.56  fof(f294,plain,(
% 1.44/0.56    ~spl7_3 | ~spl7_11 | spl7_24),
% 1.44/0.56    inference(avatar_contradiction_clause,[],[f288])).
% 1.44/0.56  fof(f288,plain,(
% 1.44/0.56    $false | (~spl7_3 | ~spl7_11 | spl7_24)),
% 1.44/0.56    inference(unit_resulting_resolution,[],[f236,f74,f138,f44])).
% 1.44/0.56  fof(f44,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X2)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f16])).
% 1.44/0.56  fof(f16,plain,(
% 1.44/0.56    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 1.44/0.56    inference(ennf_transformation,[],[f6])).
% 1.44/0.56  fof(f6,axiom,(
% 1.44/0.56    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).
% 1.44/0.56  fof(f138,plain,(
% 1.44/0.56    v1_xboole_0(sK0) | ~spl7_11),
% 1.44/0.56    inference(avatar_component_clause,[],[f136])).
% 1.44/0.56  fof(f136,plain,(
% 1.44/0.56    spl7_11 <=> v1_xboole_0(sK0)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 1.44/0.56  fof(f236,plain,(
% 1.44/0.56    ~v1_xboole_0(sK2) | spl7_24),
% 1.44/0.56    inference(avatar_component_clause,[],[f235])).
% 1.44/0.56  fof(f235,plain,(
% 1.44/0.56    spl7_24 <=> v1_xboole_0(sK2)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 1.44/0.56  fof(f293,plain,(
% 1.44/0.56    ~spl7_2 | ~spl7_11 | spl7_16),
% 1.44/0.56    inference(avatar_contradiction_clause,[],[f287])).
% 1.44/0.56  fof(f287,plain,(
% 1.44/0.56    $false | (~spl7_2 | ~spl7_11 | spl7_16)),
% 1.44/0.56    inference(unit_resulting_resolution,[],[f160,f69,f138,f44])).
% 1.44/0.56  fof(f160,plain,(
% 1.44/0.56    ~v1_xboole_0(sK1) | spl7_16),
% 1.44/0.56    inference(avatar_component_clause,[],[f159])).
% 1.44/0.56  fof(f159,plain,(
% 1.44/0.56    spl7_16 <=> v1_xboole_0(sK1)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 1.44/0.56  fof(f286,plain,(
% 1.44/0.56    spl7_28 | ~spl7_12 | ~spl7_14),
% 1.44/0.56    inference(avatar_split_clause,[],[f228,f150,f140,f284])).
% 1.44/0.56  fof(f140,plain,(
% 1.44/0.56    spl7_12 <=> ! [X0] : (k11_relat_1(sK1,X0) = k11_relat_1(sK2,X0) | ~m1_subset_1(X0,sK0))),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 1.44/0.56  fof(f150,plain,(
% 1.44/0.56    spl7_14 <=> ! [X0] : (m1_subset_1(sK3(sK0,sK0,sK1,X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | r2_relset_1(sK0,sK0,sK1,X0))),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 1.44/0.56  fof(f228,plain,(
% 1.44/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | r2_relset_1(sK0,sK0,sK1,X0) | k11_relat_1(sK1,sK3(sK0,sK0,sK1,X0)) = k11_relat_1(sK2,sK3(sK0,sK0,sK1,X0))) ) | (~spl7_12 | ~spl7_14)),
% 1.44/0.56    inference(resolution,[],[f151,f141])).
% 1.44/0.56  fof(f141,plain,(
% 1.44/0.56    ( ! [X0] : (~m1_subset_1(X0,sK0) | k11_relat_1(sK1,X0) = k11_relat_1(sK2,X0)) ) | ~spl7_12),
% 1.44/0.56    inference(avatar_component_clause,[],[f140])).
% 1.44/0.56  fof(f151,plain,(
% 1.44/0.56    ( ! [X0] : (m1_subset_1(sK3(sK0,sK0,sK1,X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | r2_relset_1(sK0,sK0,sK1,X0)) ) | ~spl7_14),
% 1.44/0.56    inference(avatar_component_clause,[],[f150])).
% 1.44/0.56  fof(f262,plain,(
% 1.44/0.56    spl7_26 | ~spl7_24),
% 1.44/0.56    inference(avatar_split_clause,[],[f245,f235,f259])).
% 1.44/0.56  fof(f259,plain,(
% 1.44/0.56    spl7_26 <=> k1_xboole_0 = sK2),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 1.44/0.56  fof(f245,plain,(
% 1.44/0.56    k1_xboole_0 = sK2 | ~spl7_24),
% 1.44/0.56    inference(resolution,[],[f237,f38])).
% 1.44/0.56  fof(f38,plain,(
% 1.44/0.56    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.44/0.56    inference(cnf_transformation,[],[f14])).
% 1.44/0.56  fof(f14,plain,(
% 1.44/0.56    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.44/0.56    inference(ennf_transformation,[],[f1])).
% 1.44/0.56  fof(f1,axiom,(
% 1.44/0.56    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).
% 1.44/0.56  fof(f237,plain,(
% 1.44/0.56    v1_xboole_0(sK2) | ~spl7_24),
% 1.44/0.56    inference(avatar_component_clause,[],[f235])).
% 1.44/0.56  fof(f196,plain,(
% 1.44/0.56    ~spl7_21 | spl7_1 | ~spl7_16),
% 1.44/0.56    inference(avatar_split_clause,[],[f179,f159,f62,f193])).
% 1.44/0.56  fof(f193,plain,(
% 1.44/0.56    spl7_21 <=> r2_relset_1(sK0,sK0,k1_xboole_0,sK2)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 1.44/0.56  fof(f179,plain,(
% 1.44/0.56    ~r2_relset_1(sK0,sK0,k1_xboole_0,sK2) | (spl7_1 | ~spl7_16)),
% 1.44/0.56    inference(backward_demodulation,[],[f64,f173])).
% 1.44/0.56  fof(f173,plain,(
% 1.44/0.56    k1_xboole_0 = sK1 | ~spl7_16),
% 1.44/0.56    inference(resolution,[],[f161,f38])).
% 1.44/0.56  fof(f161,plain,(
% 1.44/0.56    v1_xboole_0(sK1) | ~spl7_16),
% 1.44/0.56    inference(avatar_component_clause,[],[f159])).
% 1.44/0.56  fof(f152,plain,(
% 1.44/0.56    spl7_14 | ~spl7_2),
% 1.44/0.56    inference(avatar_split_clause,[],[f114,f67,f150])).
% 1.44/0.56  fof(f114,plain,(
% 1.44/0.56    ( ! [X0] : (m1_subset_1(sK3(sK0,sK0,sK1,X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | r2_relset_1(sK0,sK0,sK1,X0)) ) | ~spl7_2),
% 1.44/0.56    inference(resolution,[],[f49,f69])).
% 1.44/0.56  fof(f49,plain,(
% 1.44/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(sK3(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X3)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f31])).
% 1.44/0.56  fof(f147,plain,(
% 1.44/0.56    spl7_13 | ~spl7_5),
% 1.44/0.56    inference(avatar_split_clause,[],[f98,f90,f145])).
% 1.44/0.56  fof(f98,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | r2_hidden(X1,k11_relat_1(sK2,X0))) ) | ~spl7_5),
% 1.44/0.56    inference(resolution,[],[f92,f45])).
% 1.44/0.56  fof(f45,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k11_relat_1(X2,X0))) )),
% 1.44/0.56    inference(cnf_transformation,[],[f25])).
% 1.44/0.56  fof(f142,plain,(
% 1.44/0.56    spl7_11 | spl7_12),
% 1.44/0.56    inference(avatar_split_clause,[],[f79,f140,f136])).
% 1.44/0.56  fof(f79,plain,(
% 1.44/0.56    ( ! [X0] : (k11_relat_1(sK1,X0) = k11_relat_1(sK2,X0) | ~m1_subset_1(X0,sK0) | v1_xboole_0(sK0)) )),
% 1.44/0.56    inference(resolution,[],[f35,f40])).
% 1.44/0.56  fof(f40,plain,(
% 1.44/0.56    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f24])).
% 1.44/0.56  fof(f24,plain,(
% 1.44/0.56    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.44/0.56    inference(nnf_transformation,[],[f15])).
% 1.44/0.56  fof(f15,plain,(
% 1.44/0.56    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.44/0.56    inference(ennf_transformation,[],[f2])).
% 1.44/0.56  fof(f2,axiom,(
% 1.44/0.56    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.44/0.56  fof(f35,plain,(
% 1.44/0.56    ( ! [X3] : (~r2_hidden(X3,sK0) | k11_relat_1(sK1,X3) = k11_relat_1(sK2,X3)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f23])).
% 1.44/0.56  fof(f23,plain,(
% 1.44/0.56    (~r2_relset_1(sK0,sK0,sK1,sK2) & ! [X3] : (k11_relat_1(sK1,X3) = k11_relat_1(sK2,X3) | ~r2_hidden(X3,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.44/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f22,f21])).
% 1.44/0.56  fof(f21,plain,(
% 1.44/0.56    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X1,X2) & ! [X3] : (k11_relat_1(X1,X3) = k11_relat_1(X2,X3) | ~r2_hidden(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) => (? [X2] : (~r2_relset_1(sK0,sK0,sK1,X2) & ! [X3] : (k11_relat_1(X2,X3) = k11_relat_1(sK1,X3) | ~r2_hidden(X3,sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))),
% 1.44/0.56    introduced(choice_axiom,[])).
% 1.44/0.56  fof(f22,plain,(
% 1.44/0.56    ? [X2] : (~r2_relset_1(sK0,sK0,sK1,X2) & ! [X3] : (k11_relat_1(X2,X3) = k11_relat_1(sK1,X3) | ~r2_hidden(X3,sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))) => (~r2_relset_1(sK0,sK0,sK1,sK2) & ! [X3] : (k11_relat_1(sK1,X3) = k11_relat_1(sK2,X3) | ~r2_hidden(X3,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))),
% 1.44/0.56    introduced(choice_axiom,[])).
% 1.44/0.56  fof(f12,plain,(
% 1.44/0.56    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X1,X2) & ! [X3] : (k11_relat_1(X1,X3) = k11_relat_1(X2,X3) | ~r2_hidden(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 1.44/0.56    inference(flattening,[],[f11])).
% 1.44/0.56  fof(f11,plain,(
% 1.44/0.56    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X1,X2) & ! [X3] : (k11_relat_1(X1,X3) = k11_relat_1(X2,X3) | ~r2_hidden(X3,X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 1.44/0.56    inference(ennf_transformation,[],[f10])).
% 1.44/0.56  fof(f10,negated_conjecture,(
% 1.44/0.56    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => (! [X3] : (r2_hidden(X3,X0) => k11_relat_1(X1,X3) = k11_relat_1(X2,X3)) => r2_relset_1(X0,X0,X1,X2))))),
% 1.44/0.56    inference(negated_conjecture,[],[f9])).
% 1.44/0.56  fof(f9,conjecture,(
% 1.44/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => (! [X3] : (r2_hidden(X3,X0) => k11_relat_1(X1,X3) = k11_relat_1(X2,X3)) => r2_relset_1(X0,X0,X1,X2))))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relset_1)).
% 1.44/0.56  fof(f134,plain,(
% 1.44/0.56    spl7_10 | ~spl7_4),
% 1.44/0.56    inference(avatar_split_clause,[],[f95,f83,f132])).
% 1.44/0.56  fof(f95,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | r2_hidden(X1,k11_relat_1(sK1,X0))) ) | ~spl7_4),
% 1.44/0.56    inference(resolution,[],[f85,f45])).
% 1.44/0.56  fof(f111,plain,(
% 1.44/0.56    spl7_7 | ~spl7_3),
% 1.44/0.56    inference(avatar_split_clause,[],[f88,f72,f108])).
% 1.44/0.56  fof(f108,plain,(
% 1.44/0.56    spl7_7 <=> r2_relset_1(sK0,sK0,sK2,sK2)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.44/0.56  fof(f88,plain,(
% 1.44/0.56    r2_relset_1(sK0,sK0,sK2,sK2) | ~spl7_3),
% 1.44/0.56    inference(resolution,[],[f60,f74])).
% 1.44/0.56  fof(f60,plain,(
% 1.44/0.56    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.44/0.56    inference(duplicate_literal_removal,[],[f55])).
% 1.44/0.56  fof(f55,plain,(
% 1.44/0.56    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.44/0.56    inference(equality_resolution,[],[f54])).
% 1.44/0.56  fof(f54,plain,(
% 1.44/0.56    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.44/0.56    inference(cnf_transformation,[],[f32])).
% 1.44/0.56  fof(f32,plain,(
% 1.44/0.56    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.56    inference(nnf_transformation,[],[f20])).
% 1.44/0.56  fof(f20,plain,(
% 1.44/0.56    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.56    inference(flattening,[],[f19])).
% 1.44/0.56  fof(f19,plain,(
% 1.44/0.56    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.44/0.56    inference(ennf_transformation,[],[f8])).
% 1.44/0.56  fof(f8,axiom,(
% 1.44/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.44/0.56  fof(f93,plain,(
% 1.44/0.56    spl7_5 | ~spl7_3),
% 1.44/0.56    inference(avatar_split_clause,[],[f81,f72,f90])).
% 1.44/0.56  fof(f81,plain,(
% 1.44/0.56    v1_relat_1(sK2) | ~spl7_3),
% 1.44/0.56    inference(resolution,[],[f76,f74])).
% 1.44/0.56  fof(f76,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) )),
% 1.44/0.56    inference(resolution,[],[f37,f39])).
% 1.44/0.56  fof(f39,plain,(
% 1.44/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.44/0.56    inference(cnf_transformation,[],[f4])).
% 1.44/0.56  fof(f4,axiom,(
% 1.44/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.44/0.56  fof(f37,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f13])).
% 1.44/0.56  fof(f13,plain,(
% 1.44/0.56    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.44/0.56    inference(ennf_transformation,[],[f3])).
% 1.44/0.56  fof(f3,axiom,(
% 1.44/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.44/0.56  fof(f86,plain,(
% 1.44/0.56    spl7_4 | ~spl7_2),
% 1.44/0.56    inference(avatar_split_clause,[],[f80,f67,f83])).
% 1.44/0.56  fof(f80,plain,(
% 1.44/0.56    v1_relat_1(sK1) | ~spl7_2),
% 1.44/0.56    inference(resolution,[],[f76,f69])).
% 1.44/0.56  fof(f75,plain,(
% 1.44/0.56    spl7_3),
% 1.44/0.56    inference(avatar_split_clause,[],[f34,f72])).
% 1.44/0.56  fof(f34,plain,(
% 1.44/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.44/0.56    inference(cnf_transformation,[],[f23])).
% 1.44/0.56  fof(f70,plain,(
% 1.44/0.56    spl7_2),
% 1.44/0.56    inference(avatar_split_clause,[],[f33,f67])).
% 1.44/0.56  fof(f33,plain,(
% 1.44/0.56    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.44/0.56    inference(cnf_transformation,[],[f23])).
% 1.44/0.56  fof(f65,plain,(
% 1.44/0.56    ~spl7_1),
% 1.44/0.56    inference(avatar_split_clause,[],[f36,f62])).
% 1.44/0.56  fof(f36,plain,(
% 1.44/0.56    ~r2_relset_1(sK0,sK0,sK1,sK2)),
% 1.44/0.56    inference(cnf_transformation,[],[f23])).
% 1.44/0.56  % SZS output end Proof for theBenchmark
% 1.44/0.56  % (20858)------------------------------
% 1.44/0.56  % (20858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (20858)Termination reason: Refutation
% 1.44/0.56  
% 1.44/0.56  % (20858)Memory used [KB]: 7036
% 1.44/0.56  % (20858)Time elapsed: 0.169 s
% 1.44/0.56  % (20858)------------------------------
% 1.44/0.56  % (20858)------------------------------
% 1.44/0.56  % (20855)Success in time 0.219 s
%------------------------------------------------------------------------------
