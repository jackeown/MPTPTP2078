%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t145_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:31 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  203 ( 482 expanded)
%              Number of leaves         :   40 ( 185 expanded)
%              Depth                    :   14
%              Number of atoms          :  900 (1999 expanded)
%              Number of equality atoms :  127 ( 370 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1227,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f99,f103,f110,f114,f118,f144,f151,f157,f187,f201,f250,f254,f259,f263,f267,f287,f329,f339,f421,f598,f606,f634,f643,f825,f826,f878,f941,f1195,f1196,f1211,f1226])).

fof(f1226,plain,
    ( spl7_130
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_14
    | spl7_17
    | ~ spl7_20
    | ~ spl7_44
    | ~ spl7_180 ),
    inference(avatar_split_clause,[],[f1214,f828,f252,f155,f146,f142,f97,f93,f596])).

fof(f596,plain,
    ( spl7_130
  <=> r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_130])])).

fof(f93,plain,
    ( spl7_0
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_0])])).

fof(f97,plain,
    ( spl7_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f142,plain,
    ( spl7_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f146,plain,
    ( spl7_17
  <=> ~ r1_partfun1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f155,plain,
    ( spl7_20
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f252,plain,
    ( spl7_44
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f828,plain,
    ( spl7_180
  <=> k1_relat_1(sK3) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_180])])).

fof(f1214,plain,
    ( r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_14
    | ~ spl7_17
    | ~ spl7_20
    | ~ spl7_44
    | ~ spl7_180 ),
    inference(subsumption_resolution,[],[f1213,f147])).

fof(f147,plain,
    ( ~ r1_partfun1(sK2,sK3)
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f146])).

fof(f1213,plain,
    ( r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))
    | r1_partfun1(sK2,sK3)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_14
    | ~ spl7_20
    | ~ spl7_44
    | ~ spl7_180 ),
    inference(subsumption_resolution,[],[f1212,f156])).

fof(f156,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f155])).

fof(f1212,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))
    | r1_partfun1(sK2,sK3)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_14
    | ~ spl7_44
    | ~ spl7_180 ),
    inference(subsumption_resolution,[],[f1154,f98])).

fof(f98,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f1154,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))
    | r1_partfun1(sK2,sK3)
    | ~ spl7_0
    | ~ spl7_14
    | ~ spl7_44
    | ~ spl7_180 ),
    inference(resolution,[],[f927,f253])).

fof(f253,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f252])).

fof(f927,plain,
    ( ! [X5] :
        ( ~ r1_tarski(k1_relat_1(X5),sK0)
        | ~ v1_funct_1(X5)
        | ~ v1_relat_1(X5)
        | r2_hidden(sK5(X5,sK3),k1_relat_1(X5))
        | r1_partfun1(X5,sK3) )
    | ~ spl7_0
    | ~ spl7_14
    | ~ spl7_180 ),
    inference(subsumption_resolution,[],[f926,f94])).

fof(f94,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_0 ),
    inference(avatar_component_clause,[],[f93])).

fof(f926,plain,
    ( ! [X5] :
        ( ~ r1_tarski(k1_relat_1(X5),sK0)
        | ~ v1_funct_1(X5)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(X5)
        | r2_hidden(sK5(X5,sK3),k1_relat_1(X5))
        | r1_partfun1(X5,sK3) )
    | ~ spl7_14
    | ~ spl7_180 ),
    inference(subsumption_resolution,[],[f914,f143])).

fof(f143,plain,
    ( v1_relat_1(sK3)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f142])).

fof(f914,plain,
    ( ! [X5] :
        ( ~ r1_tarski(k1_relat_1(X5),sK0)
        | ~ v1_funct_1(X5)
        | ~ v1_relat_1(sK3)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(X5)
        | r2_hidden(sK5(X5,sK3),k1_relat_1(X5))
        | r1_partfun1(X5,sK3) )
    | ~ spl7_180 ),
    inference(superposition,[],[f62,f829])).

fof(f829,plain,
    ( k1_relat_1(sK3) = sK0
    | ~ spl7_180 ),
    inference(avatar_component_clause,[],[f828])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | r1_partfun1(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_partfun1(X0,X1)
          <=> ! [X2] :
                ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                | ~ r2_hidden(X2,k1_relat_1(X0)) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_partfun1(X0,X1)
          <=> ! [X2] :
                ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                | ~ r2_hidden(X2,k1_relat_1(X0)) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
           => ( r1_partfun1(X0,X1)
            <=> ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t145_funct_2.p',t132_partfun1)).

fof(f1211,plain,
    ( ~ spl7_0
    | ~ spl7_2
    | ~ spl7_14
    | spl7_17
    | ~ spl7_20
    | ~ spl7_44
    | ~ spl7_62
    | ~ spl7_130
    | ~ spl7_180 ),
    inference(avatar_contradiction_clause,[],[f1210])).

fof(f1210,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_14
    | ~ spl7_17
    | ~ spl7_20
    | ~ spl7_44
    | ~ spl7_62
    | ~ spl7_130
    | ~ spl7_180 ),
    inference(subsumption_resolution,[],[f1209,f1208])).

fof(f1208,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_14
    | ~ spl7_17
    | ~ spl7_20
    | ~ spl7_44
    | ~ spl7_180 ),
    inference(subsumption_resolution,[],[f1198,f147])).

fof(f1198,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))
    | r1_partfun1(sK2,sK3)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_14
    | ~ spl7_20
    | ~ spl7_44
    | ~ spl7_180 ),
    inference(subsumption_resolution,[],[f1197,f156])).

fof(f1197,plain,
    ( ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))
    | r1_partfun1(sK2,sK3)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_14
    | ~ spl7_44
    | ~ spl7_180 ),
    inference(subsumption_resolution,[],[f1182,f98])).

fof(f1182,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))
    | r1_partfun1(sK2,sK3)
    | ~ spl7_0
    | ~ spl7_14
    | ~ spl7_44
    | ~ spl7_180 ),
    inference(resolution,[],[f931,f253])).

fof(f931,plain,
    ( ! [X7] :
        ( ~ r1_tarski(k1_relat_1(X7),sK0)
        | ~ v1_funct_1(X7)
        | ~ v1_relat_1(X7)
        | k1_funct_1(sK3,sK5(X7,sK3)) != k1_funct_1(X7,sK5(X7,sK3))
        | r1_partfun1(X7,sK3) )
    | ~ spl7_0
    | ~ spl7_14
    | ~ spl7_180 ),
    inference(subsumption_resolution,[],[f930,f94])).

fof(f930,plain,
    ( ! [X7] :
        ( ~ r1_tarski(k1_relat_1(X7),sK0)
        | ~ v1_funct_1(X7)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(X7)
        | k1_funct_1(sK3,sK5(X7,sK3)) != k1_funct_1(X7,sK5(X7,sK3))
        | r1_partfun1(X7,sK3) )
    | ~ spl7_14
    | ~ spl7_180 ),
    inference(subsumption_resolution,[],[f916,f143])).

fof(f916,plain,
    ( ! [X7] :
        ( ~ r1_tarski(k1_relat_1(X7),sK0)
        | ~ v1_funct_1(X7)
        | ~ v1_relat_1(sK3)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(X7)
        | k1_funct_1(sK3,sK5(X7,sK3)) != k1_funct_1(X7,sK5(X7,sK3))
        | r1_partfun1(X7,sK3) )
    | ~ spl7_180 ),
    inference(superposition,[],[f63,f829])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1))
      | r1_partfun1(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1209,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_14
    | ~ spl7_20
    | ~ spl7_44
    | ~ spl7_62
    | ~ spl7_130
    | ~ spl7_180 ),
    inference(resolution,[],[f1200,f597])).

fof(f597,plain,
    ( r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))
    | ~ spl7_130 ),
    inference(avatar_component_clause,[],[f596])).

fof(f1200,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_relat_1(sK2))
        | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) )
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_14
    | ~ spl7_20
    | ~ spl7_44
    | ~ spl7_62
    | ~ spl7_180 ),
    inference(subsumption_resolution,[],[f1199,f1170])).

fof(f1170,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK2))
        | k1_funct_1(sK2,X1) = k1_funct_1(sK3,X1)
        | ~ r1_partfun1(sK2,sK3) )
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_14
    | ~ spl7_20
    | ~ spl7_44
    | ~ spl7_180 ),
    inference(subsumption_resolution,[],[f1169,f156])).

fof(f1169,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(sK2)
        | ~ r2_hidden(X1,k1_relat_1(sK2))
        | k1_funct_1(sK2,X1) = k1_funct_1(sK3,X1)
        | ~ r1_partfun1(sK2,sK3) )
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_14
    | ~ spl7_44
    | ~ spl7_180 ),
    inference(subsumption_resolution,[],[f1167,f98])).

fof(f1167,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | ~ r2_hidden(X1,k1_relat_1(sK2))
        | k1_funct_1(sK2,X1) = k1_funct_1(sK3,X1)
        | ~ r1_partfun1(sK2,sK3) )
    | ~ spl7_0
    | ~ spl7_14
    | ~ spl7_44
    | ~ spl7_180 ),
    inference(resolution,[],[f922,f253])).

fof(f922,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(k1_relat_1(X2),sK0)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | ~ r2_hidden(X3,k1_relat_1(X2))
        | k1_funct_1(sK3,X3) = k1_funct_1(X2,X3)
        | ~ r1_partfun1(X2,sK3) )
    | ~ spl7_0
    | ~ spl7_14
    | ~ spl7_180 ),
    inference(subsumption_resolution,[],[f921,f94])).

fof(f921,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(k1_relat_1(X2),sK0)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(X2)
        | ~ r2_hidden(X3,k1_relat_1(X2))
        | k1_funct_1(sK3,X3) = k1_funct_1(X2,X3)
        | ~ r1_partfun1(X2,sK3) )
    | ~ spl7_14
    | ~ spl7_180 ),
    inference(subsumption_resolution,[],[f912,f143])).

fof(f912,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(k1_relat_1(X2),sK0)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(sK3)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(X2)
        | ~ r2_hidden(X3,k1_relat_1(X2))
        | k1_funct_1(sK3,X3) = k1_funct_1(X2,X3)
        | ~ r1_partfun1(X2,sK3) )
    | ~ spl7_180 ),
    inference(superposition,[],[f61,f829])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
      | ~ r1_partfun1(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1199,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_relat_1(sK2))
        | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
        | r1_partfun1(sK2,sK3) )
    | ~ spl7_62 ),
    inference(forward_demodulation,[],[f54,f338])).

fof(f338,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl7_62 ),
    inference(avatar_component_clause,[],[f337])).

fof(f337,plain,
    ( spl7_62
  <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).

fof(f54,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_relset_1(sK0,sK1,sK2))
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
      | r1_partfun1(sK2,sK3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( r1_partfun1(X2,X3)
          <~> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( r1_partfun1(X2,X3)
          <~> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ( k1_xboole_0 = X1
               => k1_xboole_0 = X0 )
             => ( r1_partfun1(X2,X3)
              <=> ! [X4] :
                    ( r2_hidden(X4,k1_relset_1(X0,X1,X2))
                   => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ( k1_xboole_0 = X1
             => k1_xboole_0 = X0 )
           => ( r1_partfun1(X2,X3)
            <=> ! [X4] :
                  ( r2_hidden(X4,k1_relset_1(X0,X1,X2))
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t145_funct_2.p',t145_funct_2)).

fof(f1196,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k1_relat_1(sK2)
    | r2_hidden(sK4,k1_relat_1(sK2))
    | ~ r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2)) ),
    introduced(theory_axiom,[])).

fof(f1195,plain,
    ( ~ spl7_0
    | ~ spl7_2
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_20
    | ~ spl7_44
    | ~ spl7_134
    | spl7_139
    | ~ spl7_180 ),
    inference(avatar_contradiction_clause,[],[f1194])).

fof(f1194,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_20
    | ~ spl7_44
    | ~ spl7_134
    | ~ spl7_139
    | ~ spl7_180 ),
    inference(subsumption_resolution,[],[f1193,f633])).

fof(f633,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
    | ~ spl7_139 ),
    inference(avatar_component_clause,[],[f632])).

fof(f632,plain,
    ( spl7_139
  <=> k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_139])])).

fof(f1193,plain,
    ( k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_20
    | ~ spl7_44
    | ~ spl7_134
    | ~ spl7_180 ),
    inference(resolution,[],[f1171,f620])).

fof(f620,plain,
    ( r2_hidden(sK4,k1_relat_1(sK2))
    | ~ spl7_134 ),
    inference(avatar_component_clause,[],[f619])).

fof(f619,plain,
    ( spl7_134
  <=> r2_hidden(sK4,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_134])])).

fof(f1171,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK2))
        | k1_funct_1(sK2,X1) = k1_funct_1(sK3,X1) )
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_20
    | ~ spl7_44
    | ~ spl7_180 ),
    inference(subsumption_resolution,[],[f1170,f693])).

fof(f693,plain,
    ( r1_partfun1(sK2,sK3)
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f692])).

fof(f692,plain,
    ( spl7_16
  <=> r1_partfun1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f941,plain,
    ( spl7_40
    | ~ spl7_42
    | ~ spl7_46 ),
    inference(avatar_split_clause,[],[f722,f257,f248,f236])).

fof(f236,plain,
    ( spl7_40
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f248,plain,
    ( spl7_42
  <=> v1_funct_2(sK3,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f257,plain,
    ( spl7_46
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f722,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3)
    | ~ spl7_42
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f274,f249])).

fof(f249,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f248])).

fof(f274,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3)
    | ~ v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl7_46 ),
    inference(resolution,[],[f258,f85])).

fof(f85,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t145_funct_2.p',d1_funct_2)).

fof(f258,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f257])).

fof(f878,plain,
    ( k1_relset_1(sK0,sK1,sK3) != k1_relat_1(sK3)
    | k1_relset_1(sK0,sK1,sK3) != sK0
    | k1_relat_1(sK3) = sK0 ),
    introduced(theory_axiom,[])).

fof(f826,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != sK1
    | k1_relset_1(sK0,sK1,sK3) != k1_relat_1(sK3)
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(theory_axiom,[])).

fof(f825,plain,
    ( spl7_178
    | ~ spl7_8
    | ~ spl7_42
    | ~ spl7_46 ),
    inference(avatar_split_clause,[],[f723,f257,f248,f203,f823])).

fof(f823,plain,
    ( spl7_178
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_178])])).

fof(f203,plain,
    ( spl7_8
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f723,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl7_8
    | ~ spl7_42
    | ~ spl7_46 ),
    inference(forward_demodulation,[],[f722,f204])).

fof(f204,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f203])).

fof(f643,plain,
    ( ~ spl7_0
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_14
    | ~ spl7_20
    | ~ spl7_48
    | ~ spl7_54
    | ~ spl7_64
    | ~ spl7_134
    | spl7_139 ),
    inference(avatar_contradiction_clause,[],[f642])).

fof(f642,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_14
    | ~ spl7_20
    | ~ spl7_48
    | ~ spl7_54
    | ~ spl7_64
    | ~ spl7_134
    | ~ spl7_139 ),
    inference(subsumption_resolution,[],[f640,f633])).

fof(f640,plain,
    ( k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_14
    | ~ spl7_20
    | ~ spl7_48
    | ~ spl7_54
    | ~ spl7_64
    | ~ spl7_134 ),
    inference(resolution,[],[f611,f620])).

fof(f611,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_relat_1(sK2))
        | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) )
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_14
    | ~ spl7_20
    | ~ spl7_48
    | ~ spl7_54
    | ~ spl7_64 ),
    inference(subsumption_resolution,[],[f610,f608])).

fof(f608,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
        | ~ r1_partfun1(sK2,sK3) )
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_14
    | ~ spl7_20
    | ~ spl7_48
    | ~ spl7_54 ),
    inference(subsumption_resolution,[],[f607,f156])).

fof(f607,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2)
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
        | ~ r1_partfun1(sK2,sK3) )
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_14
    | ~ spl7_48
    | ~ spl7_54 ),
    inference(subsumption_resolution,[],[f532,f98])).

fof(f532,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
        | ~ r1_partfun1(sK2,sK3) )
    | ~ spl7_0
    | ~ spl7_14
    | ~ spl7_48
    | ~ spl7_54 ),
    inference(resolution,[],[f313,f262])).

fof(f262,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_xboole_0)
    | ~ spl7_48 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl7_48
  <=> r1_tarski(k1_relat_1(sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f313,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(X0),k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(X1,k1_relat_1(X0))
        | k1_funct_1(sK3,X1) = k1_funct_1(X0,X1)
        | ~ r1_partfun1(X0,sK3) )
    | ~ spl7_0
    | ~ spl7_14
    | ~ spl7_54 ),
    inference(subsumption_resolution,[],[f312,f94])).

fof(f312,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(X0),k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(X1,k1_relat_1(X0))
        | k1_funct_1(sK3,X1) = k1_funct_1(X0,X1)
        | ~ r1_partfun1(X0,sK3) )
    | ~ spl7_14
    | ~ spl7_54 ),
    inference(subsumption_resolution,[],[f304,f143])).

fof(f304,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(X0),k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(sK3)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(X1,k1_relat_1(X0))
        | k1_funct_1(sK3,X1) = k1_funct_1(X0,X1)
        | ~ r1_partfun1(X0,sK3) )
    | ~ spl7_54 ),
    inference(superposition,[],[f61,f286])).

fof(f286,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl7_54 ),
    inference(avatar_component_clause,[],[f285])).

fof(f285,plain,
    ( spl7_54
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).

fof(f610,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_relat_1(sK2))
        | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
        | r1_partfun1(sK2,sK3) )
    | ~ spl7_6
    | ~ spl7_64 ),
    inference(forward_demodulation,[],[f609,f342])).

fof(f342,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl7_64 ),
    inference(avatar_component_clause,[],[f341])).

fof(f341,plain,
    ( spl7_64
  <=> k1_relset_1(k1_xboole_0,sK1,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f609,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_relset_1(k1_xboole_0,sK1,sK2))
        | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
        | r1_partfun1(sK2,sK3) )
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f54,f106])).

fof(f106,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl7_6
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f634,plain,
    ( ~ spl7_17
    | ~ spl7_139 ),
    inference(avatar_split_clause,[],[f53,f632,f146])).

fof(f53,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
    | ~ r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f606,plain,
    ( ~ spl7_0
    | ~ spl7_2
    | ~ spl7_12
    | ~ spl7_14
    | spl7_17
    | ~ spl7_20
    | ~ spl7_48
    | ~ spl7_54
    | ~ spl7_130 ),
    inference(avatar_contradiction_clause,[],[f605])).

fof(f605,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_17
    | ~ spl7_20
    | ~ spl7_48
    | ~ spl7_54
    | ~ spl7_130 ),
    inference(subsumption_resolution,[],[f599,f546])).

fof(f546,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_14
    | ~ spl7_17
    | ~ spl7_20
    | ~ spl7_48
    | ~ spl7_54 ),
    inference(subsumption_resolution,[],[f545,f147])).

fof(f545,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))
    | r1_partfun1(sK2,sK3)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_14
    | ~ spl7_20
    | ~ spl7_48
    | ~ spl7_54 ),
    inference(subsumption_resolution,[],[f544,f156])).

fof(f544,plain,
    ( ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))
    | r1_partfun1(sK2,sK3)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_14
    | ~ spl7_48
    | ~ spl7_54 ),
    inference(subsumption_resolution,[],[f539,f98])).

fof(f539,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))
    | r1_partfun1(sK2,sK3)
    | ~ spl7_0
    | ~ spl7_14
    | ~ spl7_48
    | ~ spl7_54 ),
    inference(resolution,[],[f323,f262])).

fof(f323,plain,
    ( ! [X6] :
        ( ~ r1_tarski(k1_relat_1(X6),k1_xboole_0)
        | ~ v1_funct_1(X6)
        | ~ v1_relat_1(X6)
        | k1_funct_1(sK3,sK5(X6,sK3)) != k1_funct_1(X6,sK5(X6,sK3))
        | r1_partfun1(X6,sK3) )
    | ~ spl7_0
    | ~ spl7_14
    | ~ spl7_54 ),
    inference(subsumption_resolution,[],[f322,f94])).

fof(f322,plain,
    ( ! [X6] :
        ( ~ r1_tarski(k1_relat_1(X6),k1_xboole_0)
        | ~ v1_funct_1(X6)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(X6)
        | k1_funct_1(sK3,sK5(X6,sK3)) != k1_funct_1(X6,sK5(X6,sK3))
        | r1_partfun1(X6,sK3) )
    | ~ spl7_14
    | ~ spl7_54 ),
    inference(subsumption_resolution,[],[f308,f143])).

fof(f308,plain,
    ( ! [X6] :
        ( ~ r1_tarski(k1_relat_1(X6),k1_xboole_0)
        | ~ v1_funct_1(X6)
        | ~ v1_relat_1(sK3)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(X6)
        | k1_funct_1(sK3,sK5(X6,sK3)) != k1_funct_1(X6,sK5(X6,sK3))
        | r1_partfun1(X6,sK3) )
    | ~ spl7_54 ),
    inference(superposition,[],[f63,f286])).

fof(f599,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3))
    | ~ spl7_12
    | ~ spl7_17
    | ~ spl7_130 ),
    inference(resolution,[],[f597,f153])).

fof(f153,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_relat_1(sK2))
        | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) )
    | ~ spl7_12
    | ~ spl7_17 ),
    inference(forward_demodulation,[],[f152,f130])).

fof(f130,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl7_12 ),
    inference(resolution,[],[f117,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t145_funct_2.p',redefinition_k1_relset_1)).

fof(f117,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl7_12
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f152,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_relset_1(sK0,sK1,sK2))
        | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) )
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f54,f147])).

fof(f598,plain,
    ( spl7_130
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_14
    | spl7_17
    | ~ spl7_20
    | ~ spl7_48
    | ~ spl7_54 ),
    inference(avatar_split_clause,[],[f526,f285,f261,f155,f146,f142,f97,f93,f596])).

fof(f526,plain,
    ( r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_14
    | ~ spl7_17
    | ~ spl7_20
    | ~ spl7_48
    | ~ spl7_54 ),
    inference(subsumption_resolution,[],[f525,f147])).

fof(f525,plain,
    ( r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))
    | r1_partfun1(sK2,sK3)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_14
    | ~ spl7_20
    | ~ spl7_48
    | ~ spl7_54 ),
    inference(subsumption_resolution,[],[f524,f156])).

fof(f524,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))
    | r1_partfun1(sK2,sK3)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_14
    | ~ spl7_48
    | ~ spl7_54 ),
    inference(subsumption_resolution,[],[f521,f98])).

fof(f521,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))
    | r1_partfun1(sK2,sK3)
    | ~ spl7_0
    | ~ spl7_14
    | ~ spl7_48
    | ~ spl7_54 ),
    inference(resolution,[],[f318,f262])).

fof(f318,plain,
    ( ! [X4] :
        ( ~ r1_tarski(k1_relat_1(X4),k1_xboole_0)
        | ~ v1_funct_1(X4)
        | ~ v1_relat_1(X4)
        | r2_hidden(sK5(X4,sK3),k1_relat_1(X4))
        | r1_partfun1(X4,sK3) )
    | ~ spl7_0
    | ~ spl7_14
    | ~ spl7_54 ),
    inference(subsumption_resolution,[],[f317,f94])).

fof(f317,plain,
    ( ! [X4] :
        ( ~ r1_tarski(k1_relat_1(X4),k1_xboole_0)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(X4)
        | r2_hidden(sK5(X4,sK3),k1_relat_1(X4))
        | r1_partfun1(X4,sK3) )
    | ~ spl7_14
    | ~ spl7_54 ),
    inference(subsumption_resolution,[],[f306,f143])).

fof(f306,plain,
    ( ! [X4] :
        ( ~ r1_tarski(k1_relat_1(X4),k1_xboole_0)
        | ~ v1_funct_1(X4)
        | ~ v1_relat_1(sK3)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(X4)
        | r2_hidden(sK5(X4,sK3),k1_relat_1(X4))
        | r1_partfun1(X4,sK3) )
    | ~ spl7_54 ),
    inference(superposition,[],[f62,f286])).

fof(f421,plain,
    ( spl7_64
    | ~ spl7_50 ),
    inference(avatar_split_clause,[],[f291,f265,f341])).

fof(f265,plain,
    ( spl7_50
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f291,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl7_50 ),
    inference(resolution,[],[f266,f77])).

fof(f266,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl7_50 ),
    inference(avatar_component_clause,[],[f265])).

fof(f339,plain,
    ( spl7_62
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f130,f116,f337])).

fof(f329,plain,
    ( spl7_58
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f120,f112,f327])).

fof(f327,plain,
    ( spl7_58
  <=> k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).

fof(f112,plain,
    ( spl7_10
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f120,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl7_10 ),
    inference(resolution,[],[f113,f77])).

fof(f113,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f112])).

fof(f287,plain,
    ( spl7_54
    | ~ spl7_40
    | ~ spl7_46 ),
    inference(avatar_split_clause,[],[f282,f257,f236,f285])).

fof(f282,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl7_40
    | ~ spl7_46 ),
    inference(forward_demodulation,[],[f276,f237])).

fof(f237,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3)
    | ~ spl7_40 ),
    inference(avatar_component_clause,[],[f236])).

fof(f276,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl7_46 ),
    inference(resolution,[],[f258,f77])).

fof(f267,plain,
    ( spl7_50
    | ~ spl7_6
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f210,f116,f105,f265])).

fof(f210,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl7_6
    | ~ spl7_12 ),
    inference(superposition,[],[f117,f106])).

fof(f263,plain,
    ( spl7_48
    | ~ spl7_6
    | ~ spl7_44 ),
    inference(avatar_split_clause,[],[f255,f252,f105,f261])).

fof(f255,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_xboole_0)
    | ~ spl7_6
    | ~ spl7_44 ),
    inference(forward_demodulation,[],[f253,f106])).

fof(f259,plain,
    ( spl7_46
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f209,f112,f105,f257])).

fof(f209,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(superposition,[],[f113,f106])).

fof(f254,plain,
    ( spl7_44
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f196,f185,f252])).

fof(f185,plain,
    ( spl7_32
  <=> m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f196,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl7_32 ),
    inference(resolution,[],[f186,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t145_funct_2.p',t3_subset)).

fof(f186,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f185])).

fof(f250,plain,
    ( spl7_42
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f208,f105,f101,f248])).

fof(f101,plain,
    ( spl7_4
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f208,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(superposition,[],[f102,f106])).

fof(f102,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f101])).

fof(f201,plain,
    ( spl7_36
    | ~ spl7_4
    | spl7_9
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f128,f112,f108,f101,f199])).

fof(f199,plain,
    ( spl7_36
  <=> k1_relset_1(sK0,sK1,sK3) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f108,plain,
    ( spl7_9
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f128,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | ~ spl7_4
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f127,f102])).

fof(f127,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f123,f109])).

fof(f109,plain,
    ( k1_xboole_0 != sK1
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f108])).

fof(f123,plain,
    ( k1_xboole_0 = sK1
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl7_10 ),
    inference(resolution,[],[f113,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f187,plain,
    ( spl7_32
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f136,f116,f185])).

fof(f136,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f131,f130])).

fof(f131,plain,
    ( m1_subset_1(k1_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))
    | ~ spl7_12 ),
    inference(resolution,[],[f117,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t145_funct_2.p',dt_k1_relset_1)).

fof(f157,plain,
    ( spl7_20
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f129,f116,f155])).

fof(f129,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_12 ),
    inference(resolution,[],[f117,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t145_funct_2.p',cc1_relset_1)).

fof(f151,plain,
    ( ~ spl7_17
    | spl7_18 ),
    inference(avatar_split_clause,[],[f52,f149,f146])).

fof(f149,plain,
    ( spl7_18
  <=> r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f52,plain,
    ( r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2))
    | ~ r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f144,plain,
    ( spl7_14
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f119,f112,f142])).

fof(f119,plain,
    ( v1_relat_1(sK3)
    | ~ spl7_10 ),
    inference(resolution,[],[f113,f83])).

fof(f118,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f60,f116])).

fof(f60,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f114,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f58,f112])).

fof(f58,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f110,plain,
    ( spl7_6
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f55,f108,f105])).

fof(f55,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f29])).

fof(f103,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f57,f101])).

fof(f57,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f99,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f59,f97])).

fof(f59,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f95,plain,(
    spl7_0 ),
    inference(avatar_split_clause,[],[f56,f93])).

fof(f56,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
