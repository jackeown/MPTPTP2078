%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t160_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:34 EDT 2019

% Result     : Theorem 56.75s
% Output     : Refutation 56.75s
% Verified   : 
% Statistics : Number of formulae       :  217 (2229 expanded)
%              Number of leaves         :   42 ( 747 expanded)
%              Depth                    :   19
%              Number of atoms          :  877 (7877 expanded)
%              Number of equality atoms :   91 (1140 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1445,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f180,f184,f188,f192,f196,f287,f381,f496,f497,f507,f514,f521,f528,f535,f544,f545,f546,f1353,f1364,f1368,f1444])).

fof(f1444,plain,
    ( ~ spl9_34
    | spl9_39
    | ~ spl9_40
    | ~ spl9_42 ),
    inference(avatar_contradiction_clause,[],[f1443])).

fof(f1443,plain,
    ( $false
    | ~ spl9_34
    | ~ spl9_39
    | ~ spl9_40
    | ~ spl9_42 ),
    inference(subsumption_resolution,[],[f1440,f1422])).

fof(f1422,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl9_34
    | ~ spl9_39
    | ~ spl9_40 ),
    inference(unit_resulting_resolution,[],[f1408,f1401,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => v1_xboole_0(k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t160_funct_2.p',fc3_funct_2)).

fof(f1401,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK0,sK1))
    | ~ spl9_34 ),
    inference(unit_resulting_resolution,[],[f412,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t160_funct_2.p',t7_boole)).

fof(f412,plain,
    ( r2_hidden(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1))
    | ~ spl9_34 ),
    inference(avatar_component_clause,[],[f411])).

fof(f411,plain,
    ( spl9_34
  <=> r2_hidden(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).

fof(f1408,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl9_39
    | ~ spl9_40 ),
    inference(unit_resulting_resolution,[],[f432,f435,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t160_funct_2.p',cc1_partfun1)).

fof(f435,plain,
    ( m1_subset_1(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl9_40 ),
    inference(avatar_component_clause,[],[f434])).

fof(f434,plain,
    ( spl9_40
  <=> m1_subset_1(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).

fof(f432,plain,
    ( ~ v1_partfun1(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)),sK0)
    | ~ spl9_39 ),
    inference(avatar_component_clause,[],[f431])).

fof(f431,plain,
    ( spl9_39
  <=> ~ v1_partfun1(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).

fof(f1440,plain,
    ( v1_xboole_0(sK1)
    | ~ spl9_34
    | ~ spl9_39
    | ~ spl9_40
    | ~ spl9_42 ),
    inference(unit_resulting_resolution,[],[f441,f432,f435,f1396,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t160_funct_2.p',cc5_funct_2)).

fof(f1396,plain,
    ( v1_funct_2(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)),sK0,sK1)
    | ~ spl9_34 ),
    inference(unit_resulting_resolution,[],[f412,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t160_funct_2.p',t121_funct_2)).

fof(f441,plain,
    ( v1_funct_1(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)))
    | ~ spl9_42 ),
    inference(avatar_component_clause,[],[f440])).

fof(f440,plain,
    ( spl9_42
  <=> v1_funct_1(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).

fof(f1368,plain,
    ( ~ spl9_39
    | ~ spl9_35
    | ~ spl9_14
    | ~ spl9_36
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f1367,f434,f422,f194,f408,f431])).

fof(f408,plain,
    ( spl9_35
  <=> ~ r2_hidden(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).

fof(f194,plain,
    ( spl9_14
  <=> ! [X5] :
        ( k1_funct_2(sK0,sK1) != X5
        | ~ r2_hidden(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X5),X5)
        | ~ v1_funct_1(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X5))
        | ~ m1_subset_1(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X5),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_partfun1(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X5),sK0)
        | ~ r1_partfun1(k3_partfun1(k1_xboole_0,sK0,sK1),sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f422,plain,
    ( spl9_36
  <=> r1_partfun1(k3_partfun1(k1_xboole_0,sK0,sK1),sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).

fof(f1367,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1))
    | ~ v1_partfun1(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)),sK0)
    | ~ spl9_14
    | ~ spl9_36
    | ~ spl9_40 ),
    inference(subsumption_resolution,[],[f1366,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(X2)
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f1366,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1))
    | ~ v1_funct_1(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)))
    | ~ v1_partfun1(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)),sK0)
    | ~ spl9_14
    | ~ spl9_36
    | ~ spl9_40 ),
    inference(subsumption_resolution,[],[f1365,f423])).

fof(f423,plain,
    ( r1_partfun1(k3_partfun1(k1_xboole_0,sK0,sK1),sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)))
    | ~ spl9_36 ),
    inference(avatar_component_clause,[],[f422])).

fof(f1365,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1))
    | ~ v1_funct_1(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)))
    | ~ v1_partfun1(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)),sK0)
    | ~ r1_partfun1(k3_partfun1(k1_xboole_0,sK0,sK1),sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)))
    | ~ spl9_14
    | ~ spl9_40 ),
    inference(subsumption_resolution,[],[f419,f435])).

fof(f419,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1))
    | ~ v1_funct_1(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)))
    | ~ m1_subset_1(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_partfun1(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)),sK0)
    | ~ r1_partfun1(k3_partfun1(k1_xboole_0,sK0,sK1),sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)))
    | ~ spl9_14 ),
    inference(equality_resolution,[],[f195])).

fof(f195,plain,
    ( ! [X5] :
        ( k1_funct_2(sK0,sK1) != X5
        | ~ r2_hidden(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X5),X5)
        | ~ v1_funct_1(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X5))
        | ~ m1_subset_1(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X5),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_partfun1(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X5),sK0)
        | ~ r1_partfun1(k3_partfun1(k1_xboole_0,sK0,sK1),sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X5)) )
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f194])).

fof(f1364,plain,
    ( spl9_42
    | ~ spl9_44 ),
    inference(avatar_split_clause,[],[f1363,f512,f440])).

fof(f512,plain,
    ( spl9_44
  <=> sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)) = sK5(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_44])])).

fof(f1363,plain,
    ( v1_funct_1(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)))
    | ~ spl9_44 ),
    inference(subsumption_resolution,[],[f1362,f113])).

fof(f1362,plain,
    ( v1_funct_1(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)))
    | r2_hidden(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1))
    | ~ spl9_44 ),
    inference(subsumption_resolution,[],[f1361,f352])).

fof(f352,plain,(
    ! [X0,X1] : v1_funct_1(k3_partfun1(k1_xboole_0,X0,X1)) ),
    inference(unit_resulting_resolution,[],[f343,f344,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k3_partfun1(X0,X1,X2))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k3_partfun1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(k3_partfun1(X0,X1,X2)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k3_partfun1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(k3_partfun1(X0,X1,X2)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(k3_partfun1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(k3_partfun1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t160_funct_2.p',dt_k3_partfun1)).

fof(f344,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f324,f330])).

fof(f330,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(unit_resulting_resolution,[],[f93,f92,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t160_funct_2.p',t8_boole)).

fof(f92,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t160_funct_2.p',dt_o_0_0_xboole_0)).

fof(f93,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t160_funct_2.p',fc1_xboole_0)).

fof(f324,plain,(
    v1_relat_1(o_0_0_xboole_0) ),
    inference(unit_resulting_resolution,[],[f92,f94])).

fof(f94,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t160_funct_2.p',cc1_relat_1)).

fof(f343,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f325,f330])).

fof(f325,plain,(
    v1_funct_1(o_0_0_xboole_0) ),
    inference(unit_resulting_resolution,[],[f92,f95])).

fof(f95,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t160_funct_2.p',cc1_funct_1)).

fof(f1361,plain,
    ( v1_funct_1(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)))
    | r2_hidden(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1))
    | ~ v1_funct_1(k3_partfun1(k1_xboole_0,sK0,sK1))
    | ~ spl9_44 ),
    inference(subsumption_resolution,[],[f1354,f353])).

fof(f353,plain,(
    ! [X0,X1] : m1_subset_1(k3_partfun1(k1_xboole_0,X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(unit_resulting_resolution,[],[f343,f344,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_partfun1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f1354,plain,
    ( v1_funct_1(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)))
    | r2_hidden(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1))
    | ~ m1_subset_1(k3_partfun1(k1_xboole_0,sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(k3_partfun1(k1_xboole_0,sK0,sK1))
    | ~ spl9_44 ),
    inference(subsumption_resolution,[],[f572,f91])).

fof(f91,plain,(
    k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1)) != k1_funct_2(sK0,sK1) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1)) != k1_funct_2(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f78])).

fof(f78,plain,
    ( ? [X0,X1] : k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) != k1_funct_2(X0,X1)
   => k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1)) != k1_funct_2(sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ? [X0,X1] : k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) != k1_funct_2(X0,X1) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] : k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) = k1_funct_2(X0,X1) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] : k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) = k1_funct_2(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t160_funct_2.p',t160_funct_2)).

fof(f572,plain,
    ( v1_funct_1(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)))
    | k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1)) = k1_funct_2(sK0,sK1)
    | r2_hidden(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1))
    | ~ m1_subset_1(k3_partfun1(k1_xboole_0,sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(k3_partfun1(k1_xboole_0,sK0,sK1))
    | ~ spl9_44 ),
    inference(superposition,[],[f132,f513])).

fof(f513,plain,
    ( sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)) = sK5(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1))
    | ~ spl9_44 ),
    inference(avatar_component_clause,[],[f512])).

fof(f132,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_partfun1(X0,X1,X2) = X3
      | v1_funct_1(sK5(X0,X1,X2,X3))
      | r2_hidden(sK4(X0,X1,X2,X3),X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ( ( ! [X5] :
                    ( ~ r1_partfun1(X2,X5)
                    | ~ v1_partfun1(X5,X0)
                    | sK4(X0,X1,X2,X3) != X5
                    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    | ~ v1_funct_1(X5) )
                | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
              & ( ( r1_partfun1(X2,sK5(X0,X1,X2,X3))
                  & v1_partfun1(sK5(X0,X1,X2,X3),X0)
                  & sK4(X0,X1,X2,X3) = sK5(X0,X1,X2,X3)
                  & m1_subset_1(sK5(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(sK5(X0,X1,X2,X3)) )
                | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
          & ( ! [X7] :
                ( ( r2_hidden(X7,X3)
                  | ! [X8] :
                      ( ~ r1_partfun1(X2,X8)
                      | ~ v1_partfun1(X8,X0)
                      | X7 != X8
                      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_1(X8) ) )
                & ( ( r1_partfun1(X2,sK6(X0,X1,X2,X7))
                    & v1_partfun1(sK6(X0,X1,X2,X7),X0)
                    & sK6(X0,X1,X2,X7) = X7
                    & m1_subset_1(sK6(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_1(sK6(X0,X1,X2,X7)) )
                  | ~ r2_hidden(X7,X3) ) )
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f86,f89,f88,f87])).

fof(f87,plain,(
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
              | sK4(X0,X1,X2,X3) != X5
              | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_1(X5) )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( ? [X6] :
              ( r1_partfun1(X2,X6)
              & v1_partfun1(X6,X0)
              & sK4(X0,X1,X2,X3) = X6
              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X6) )
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f88,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r1_partfun1(X2,X6)
          & v1_partfun1(X6,X0)
          & X4 = X6
          & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X6) )
     => ( r1_partfun1(X2,sK5(X0,X1,X2,X3))
        & v1_partfun1(sK5(X0,X1,X2,X3),X0)
        & sK5(X0,X1,X2,X3) = X4
        & m1_subset_1(sK5(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(sK5(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f89,plain,(
    ! [X7,X2,X1,X0] :
      ( ? [X9] :
          ( r1_partfun1(X2,X9)
          & v1_partfun1(X9,X0)
          & X7 = X9
          & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X9) )
     => ( r1_partfun1(X2,sK6(X0,X1,X2,X7))
        & v1_partfun1(sK6(X0,X1,X2,X7),X0)
        & sK6(X0,X1,X2,X7) = X7
        & m1_subset_1(sK6(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(sK6(X0,X1,X2,X7)) ) ) ),
    introduced(choice_axiom,[])).

fof(f86,plain,(
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
    inference(rectify,[],[f85])).

fof(f85,plain,(
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
    inference(nnf_transformation,[],[f74])).

fof(f74,plain,(
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
    inference(flattening,[],[f73])).

fof(f73,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/funct_2__t160_funct_2.p',d7_partfun1)).

fof(f1353,plain,
    ( ~ spl9_0
    | spl9_35
    | ~ spl9_36
    | ~ spl9_38
    | ~ spl9_40
    | ~ spl9_42 ),
    inference(avatar_contradiction_clause,[],[f1352])).

fof(f1352,plain,
    ( $false
    | ~ spl9_0
    | ~ spl9_35
    | ~ spl9_36
    | ~ spl9_38
    | ~ spl9_40
    | ~ spl9_42 ),
    inference(subsumption_resolution,[],[f1346,f1110])).

fof(f1110,plain,
    ( v1_funct_2(sK4(k1_xboole_0,k1_xboole_0,k3_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)),k1_xboole_0,k1_xboole_0)
    | ~ spl9_0
    | ~ spl9_35
    | ~ spl9_36
    | ~ spl9_38
    | ~ spl9_40
    | ~ spl9_42 ),
    inference(backward_demodulation,[],[f1049,f866])).

fof(f866,plain,
    ( v1_funct_2(sK4(sK0,k1_xboole_0,k3_partfun1(k1_xboole_0,sK0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0)),sK0,k1_xboole_0)
    | ~ spl9_0
    | ~ spl9_35
    | ~ spl9_36
    | ~ spl9_38
    | ~ spl9_40
    | ~ spl9_42 ),
    inference(backward_demodulation,[],[f802,f637])).

fof(f637,plain,
    ( v1_funct_2(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)),sK0,sK1)
    | ~ spl9_0
    | ~ spl9_36
    | ~ spl9_38
    | ~ spl9_40
    | ~ spl9_42 ),
    inference(unit_resulting_resolution,[],[f163,f353,f564,f124])).

fof(f124,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X1)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t160_funct_2.p',t158_funct_2)).

fof(f564,plain,
    ( r2_hidden(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)),k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1)))
    | ~ spl9_0
    | ~ spl9_36
    | ~ spl9_38
    | ~ spl9_40
    | ~ spl9_42 ),
    inference(unit_resulting_resolution,[],[f163,f353,f441,f423,f429,f435,f143])).

fof(f143,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(X8,k5_partfun1(X0,X1,X2))
      | ~ r1_partfun1(X2,X8)
      | ~ v1_partfun1(X8,X0)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f142])).

fof(f142,plain,(
    ! [X2,X0,X8,X3,X1] :
      ( r2_hidden(X8,X3)
      | ~ r1_partfun1(X2,X8)
      | ~ v1_partfun1(X8,X0)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X8)
      | k5_partfun1(X0,X1,X2) != X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f131])).

fof(f131,plain,(
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
    inference(cnf_transformation,[],[f90])).

fof(f429,plain,
    ( v1_partfun1(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)),sK0)
    | ~ spl9_38 ),
    inference(avatar_component_clause,[],[f428])).

fof(f428,plain,
    ( spl9_38
  <=> v1_partfun1(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).

fof(f163,plain,
    ( v1_funct_1(k3_partfun1(k1_xboole_0,sK0,sK1))
    | ~ spl9_0 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl9_0
  <=> v1_funct_1(k3_partfun1(k1_xboole_0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_0])])).

fof(f802,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_0
    | ~ spl9_35
    | ~ spl9_36
    | ~ spl9_38
    | ~ spl9_40
    | ~ spl9_42 ),
    inference(unit_resulting_resolution,[],[f441,f409,f435,f637,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => r2_hidden(X2,k1_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t160_funct_2.p',t11_funct_2)).

fof(f409,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1))
    | ~ spl9_35 ),
    inference(avatar_component_clause,[],[f408])).

fof(f1049,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_0
    | ~ spl9_35
    | ~ spl9_36
    | ~ spl9_38
    | ~ spl9_40
    | ~ spl9_42 ),
    inference(unit_resulting_resolution,[],[f93,f991,f111])).

fof(f991,plain,
    ( v1_xboole_0(sK0)
    | ~ spl9_0
    | ~ spl9_35
    | ~ spl9_36
    | ~ spl9_38
    | ~ spl9_40
    | ~ spl9_42 ),
    inference(unit_resulting_resolution,[],[f93,f352,f353,f870,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2)
        & v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => v1_xboole_0(k5_partfun1(X0,X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t160_funct_2.p',fc2_partfun1)).

fof(f870,plain,
    ( ~ v1_xboole_0(k5_partfun1(sK0,k1_xboole_0,k3_partfun1(k1_xboole_0,sK0,k1_xboole_0)))
    | ~ spl9_0
    | ~ spl9_35
    | ~ spl9_36
    | ~ spl9_38
    | ~ spl9_40
    | ~ spl9_42 ),
    inference(backward_demodulation,[],[f802,f647])).

fof(f647,plain,
    ( ~ v1_xboole_0(k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1)))
    | ~ spl9_0
    | ~ spl9_36
    | ~ spl9_38
    | ~ spl9_40
    | ~ spl9_42 ),
    inference(unit_resulting_resolution,[],[f564,f112])).

fof(f1346,plain,
    ( ~ v1_funct_2(sK4(k1_xboole_0,k1_xboole_0,k3_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)),k1_xboole_0,k1_xboole_0)
    | ~ spl9_0
    | ~ spl9_35
    | ~ spl9_36
    | ~ spl9_38
    | ~ spl9_40
    | ~ spl9_42 ),
    inference(unit_resulting_resolution,[],[f1085,f1081,f1084,f140])).

fof(f140,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,k1_funct_2(k1_xboole_0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f1084,plain,
    ( m1_subset_1(sK4(k1_xboole_0,k1_xboole_0,k3_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl9_0
    | ~ spl9_35
    | ~ spl9_36
    | ~ spl9_38
    | ~ spl9_40
    | ~ spl9_42 ),
    inference(backward_demodulation,[],[f1049,f840])).

fof(f840,plain,
    ( m1_subset_1(sK4(sK0,k1_xboole_0,k3_partfun1(k1_xboole_0,sK0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl9_0
    | ~ spl9_35
    | ~ spl9_36
    | ~ spl9_38
    | ~ spl9_40
    | ~ spl9_42 ),
    inference(backward_demodulation,[],[f802,f435])).

fof(f1081,plain,
    ( ~ r2_hidden(sK4(k1_xboole_0,k1_xboole_0,k3_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)),k1_funct_2(k1_xboole_0,k1_xboole_0))
    | ~ spl9_0
    | ~ spl9_35
    | ~ spl9_36
    | ~ spl9_38
    | ~ spl9_40
    | ~ spl9_42 ),
    inference(backward_demodulation,[],[f1049,f837])).

fof(f837,plain,
    ( ~ r2_hidden(sK4(sK0,k1_xboole_0,k3_partfun1(k1_xboole_0,sK0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0)),k1_funct_2(sK0,k1_xboole_0))
    | ~ spl9_0
    | ~ spl9_35
    | ~ spl9_36
    | ~ spl9_38
    | ~ spl9_40
    | ~ spl9_42 ),
    inference(backward_demodulation,[],[f802,f409])).

fof(f1085,plain,
    ( v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,k3_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)))
    | ~ spl9_0
    | ~ spl9_35
    | ~ spl9_36
    | ~ spl9_38
    | ~ spl9_40
    | ~ spl9_42 ),
    inference(backward_demodulation,[],[f1049,f841])).

fof(f841,plain,
    ( v1_funct_1(sK4(sK0,k1_xboole_0,k3_partfun1(k1_xboole_0,sK0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0)))
    | ~ spl9_0
    | ~ spl9_35
    | ~ spl9_36
    | ~ spl9_38
    | ~ spl9_40
    | ~ spl9_42 ),
    inference(backward_demodulation,[],[f802,f441])).

fof(f546,plain,
    ( spl9_38
    | ~ spl9_44
    | ~ spl9_50 ),
    inference(avatar_split_clause,[],[f538,f533,f512,f428])).

fof(f533,plain,
    ( spl9_50
  <=> v1_partfun1(sK5(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_50])])).

fof(f538,plain,
    ( v1_partfun1(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)),sK0)
    | ~ spl9_44
    | ~ spl9_50 ),
    inference(backward_demodulation,[],[f513,f534])).

fof(f534,plain,
    ( v1_partfun1(sK5(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)),sK0)
    | ~ spl9_50 ),
    inference(avatar_component_clause,[],[f533])).

fof(f545,plain,
    ( spl9_40
    | ~ spl9_44
    | ~ spl9_48 ),
    inference(avatar_split_clause,[],[f537,f526,f512,f434])).

fof(f526,plain,
    ( spl9_48
  <=> m1_subset_1(sK5(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).

fof(f537,plain,
    ( m1_subset_1(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl9_44
    | ~ spl9_48 ),
    inference(backward_demodulation,[],[f513,f527])).

fof(f527,plain,
    ( m1_subset_1(sK5(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl9_48 ),
    inference(avatar_component_clause,[],[f526])).

fof(f544,plain,
    ( spl9_36
    | ~ spl9_44
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f536,f519,f512,f422])).

fof(f519,plain,
    ( spl9_46
  <=> r1_partfun1(k3_partfun1(k1_xboole_0,sK0,sK1),sK5(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).

fof(f536,plain,
    ( r1_partfun1(k3_partfun1(k1_xboole_0,sK0,sK1),sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)))
    | ~ spl9_44
    | ~ spl9_46 ),
    inference(backward_demodulation,[],[f513,f520])).

fof(f520,plain,
    ( r1_partfun1(k3_partfun1(k1_xboole_0,sK0,sK1),sK5(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)))
    | ~ spl9_46 ),
    inference(avatar_component_clause,[],[f519])).

fof(f535,plain,
    ( spl9_50
    | spl9_34
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f415,f186,f411,f533])).

fof(f186,plain,
    ( spl9_10
  <=> ! [X3] :
        ( k1_funct_2(sK0,sK1) != X3
        | r2_hidden(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X3),X3)
        | v1_partfun1(sK5(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X3),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f415,plain,
    ( r2_hidden(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1))
    | v1_partfun1(sK5(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)),sK0)
    | ~ spl9_10 ),
    inference(equality_resolution,[],[f187])).

fof(f187,plain,
    ( ! [X3] :
        ( k1_funct_2(sK0,sK1) != X3
        | r2_hidden(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X3),X3)
        | v1_partfun1(sK5(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X3),sK0) )
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f186])).

fof(f528,plain,
    ( spl9_48
    | spl9_34
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f416,f178,f411,f526])).

fof(f178,plain,
    ( spl9_6
  <=> ! [X1] :
        ( k1_funct_2(sK0,sK1) != X1
        | r2_hidden(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X1),X1)
        | m1_subset_1(sK5(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f416,plain,
    ( r2_hidden(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1))
    | m1_subset_1(sK5(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl9_6 ),
    inference(equality_resolution,[],[f179])).

fof(f179,plain,
    ( ! [X1] :
        ( k1_funct_2(sK0,sK1) != X1
        | r2_hidden(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X1),X1)
        | m1_subset_1(sK5(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f178])).

fof(f521,plain,
    ( spl9_46
    | spl9_34
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f417,f190,f411,f519])).

fof(f190,plain,
    ( spl9_12
  <=> ! [X4] :
        ( k1_funct_2(sK0,sK1) != X4
        | r2_hidden(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X4),X4)
        | r1_partfun1(k3_partfun1(k1_xboole_0,sK0,sK1),sK5(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f417,plain,
    ( r2_hidden(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1))
    | r1_partfun1(k3_partfun1(k1_xboole_0,sK0,sK1),sK5(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)))
    | ~ spl9_12 ),
    inference(equality_resolution,[],[f191])).

fof(f191,plain,
    ( ! [X4] :
        ( k1_funct_2(sK0,sK1) != X4
        | r2_hidden(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X4),X4)
        | r1_partfun1(k3_partfun1(k1_xboole_0,sK0,sK1),sK5(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X4)) )
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f190])).

fof(f514,plain,
    ( spl9_44
    | spl9_34
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f418,f182,f411,f512])).

fof(f182,plain,
    ( spl9_8
  <=> ! [X2] :
        ( k1_funct_2(sK0,sK1) != X2
        | r2_hidden(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X2),X2)
        | sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X2) = sK5(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f418,plain,
    ( r2_hidden(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1))
    | sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)) = sK5(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1))
    | ~ spl9_8 ),
    inference(equality_resolution,[],[f183])).

fof(f183,plain,
    ( ! [X2] :
        ( k1_funct_2(sK0,sK1) != X2
        | r2_hidden(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X2),X2)
        | sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X2) = sK5(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X2) )
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f182])).

fof(f507,plain,
    ( spl9_37
    | ~ spl9_40
    | ~ spl9_42 ),
    inference(avatar_contradiction_clause,[],[f506])).

fof(f506,plain,
    ( $false
    | ~ spl9_37
    | ~ spl9_40
    | ~ spl9_42 ),
    inference(subsumption_resolution,[],[f503,f500])).

fof(f500,plain,
    ( ~ v1_relat_1(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)))
    | ~ spl9_37
    | ~ spl9_42 ),
    inference(unit_resulting_resolution,[],[f441,f426,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( r1_partfun1(k3_partfun1(k1_xboole_0,X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( r1_partfun1(k3_partfun1(k1_xboole_0,X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( r1_partfun1(k3_partfun1(k1_xboole_0,X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => r1_partfun1(k3_partfun1(k1_xboole_0,X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t160_funct_2.p',t142_partfun1)).

fof(f426,plain,
    ( ~ r1_partfun1(k3_partfun1(k1_xboole_0,sK0,sK1),sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)))
    | ~ spl9_37 ),
    inference(avatar_component_clause,[],[f425])).

fof(f425,plain,
    ( spl9_37
  <=> ~ r1_partfun1(k3_partfun1(k1_xboole_0,sK0,sK1),sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).

fof(f503,plain,
    ( v1_relat_1(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)))
    | ~ spl9_40 ),
    inference(unit_resulting_resolution,[],[f435,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t160_funct_2.p',cc1_relset_1)).

fof(f497,plain,
    ( spl9_42
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f486,f411,f440])).

fof(f486,plain,
    ( v1_funct_1(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)))
    | ~ spl9_34 ),
    inference(unit_resulting_resolution,[],[f412,f113])).

fof(f496,plain,
    ( spl9_40
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f488,f411,f434])).

fof(f488,plain,
    ( m1_subset_1(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),k1_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl9_34 ),
    inference(unit_resulting_resolution,[],[f412,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f381,plain,(
    spl9_3 ),
    inference(avatar_contradiction_clause,[],[f380])).

fof(f380,plain,
    ( $false
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f369,f343])).

fof(f369,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ spl9_3 ),
    inference(unit_resulting_resolution,[],[f344,f172,f120])).

fof(f172,plain,
    ( ~ m1_subset_1(k3_partfun1(k1_xboole_0,sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl9_3
  <=> ~ m1_subset_1(k3_partfun1(k1_xboole_0,sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f287,plain,(
    spl9_1 ),
    inference(avatar_contradiction_clause,[],[f286])).

fof(f286,plain,
    ( $false
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f283,f271])).

fof(f271,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl9_1 ),
    inference(forward_demodulation,[],[f270,f255])).

fof(f255,plain,
    ( k1_xboole_0 = k1_funct_2(k3_partfun1(k1_xboole_0,sK0,sK1),k1_xboole_0)
    | ~ spl9_1 ),
    inference(backward_demodulation,[],[f246,f233])).

fof(f233,plain,
    ( k1_xboole_0 = k1_funct_2(k3_partfun1(k1_xboole_0,sK0,sK1),o_0_0_xboole_0)
    | ~ spl9_1 ),
    inference(unit_resulting_resolution,[],[f93,f203,f111])).

fof(f203,plain,
    ( v1_xboole_0(k1_funct_2(k3_partfun1(k1_xboole_0,sK0,sK1),o_0_0_xboole_0))
    | ~ spl9_1 ),
    inference(unit_resulting_resolution,[],[f92,f198,f106])).

fof(f198,plain,
    ( ~ v1_xboole_0(k3_partfun1(k1_xboole_0,sK0,sK1))
    | ~ spl9_1 ),
    inference(unit_resulting_resolution,[],[f166,f95])).

fof(f166,plain,
    ( ~ v1_funct_1(k3_partfun1(k1_xboole_0,sK0,sK1))
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl9_1
  <=> ~ v1_funct_1(k3_partfun1(k1_xboole_0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f246,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl9_1 ),
    inference(forward_demodulation,[],[f232,f233])).

fof(f232,plain,
    ( k1_funct_2(k3_partfun1(k1_xboole_0,sK0,sK1),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl9_1 ),
    inference(unit_resulting_resolution,[],[f92,f203,f111])).

fof(f270,plain,
    ( v1_relat_1(k1_funct_2(k3_partfun1(k1_xboole_0,sK0,sK1),k1_xboole_0))
    | ~ spl9_1 ),
    inference(forward_demodulation,[],[f223,f246])).

fof(f223,plain,
    ( v1_relat_1(k1_funct_2(k3_partfun1(k1_xboole_0,sK0,sK1),o_0_0_xboole_0))
    | ~ spl9_1 ),
    inference(unit_resulting_resolution,[],[f203,f94])).

fof(f283,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ spl9_1 ),
    inference(unit_resulting_resolution,[],[f166,f269,f119])).

fof(f269,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl9_1 ),
    inference(forward_demodulation,[],[f268,f255])).

fof(f268,plain,
    ( v1_funct_1(k1_funct_2(k3_partfun1(k1_xboole_0,sK0,sK1),k1_xboole_0))
    | ~ spl9_1 ),
    inference(forward_demodulation,[],[f224,f246])).

fof(f224,plain,
    ( v1_funct_1(k1_funct_2(k3_partfun1(k1_xboole_0,sK0,sK1),o_0_0_xboole_0))
    | ~ spl9_1 ),
    inference(unit_resulting_resolution,[],[f203,f95])).

fof(f196,plain,
    ( ~ spl9_1
    | ~ spl9_3
    | spl9_14 ),
    inference(avatar_split_clause,[],[f160,f194,f171,f165])).

fof(f160,plain,(
    ! [X5] :
      ( k1_funct_2(sK0,sK1) != X5
      | ~ r1_partfun1(k3_partfun1(k1_xboole_0,sK0,sK1),sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X5))
      | ~ v1_partfun1(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X5),sK0)
      | ~ m1_subset_1(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X5),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X5))
      | ~ r2_hidden(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X5),X5)
      | ~ m1_subset_1(k3_partfun1(k1_xboole_0,sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(k3_partfun1(k1_xboole_0,sK0,sK1)) ) ),
    inference(superposition,[],[f91,f141])).

fof(f141,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_partfun1(X0,X1,X2) = X3
      | ~ r1_partfun1(X2,sK4(X0,X1,X2,X3))
      | ~ v1_partfun1(sK4(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(sK4(X0,X1,X2,X3))
      | ~ r2_hidden(sK4(X0,X1,X2,X3),X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f137])).

fof(f137,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( k5_partfun1(X0,X1,X2) = X3
      | ~ r1_partfun1(X2,X5)
      | ~ v1_partfun1(X5,X0)
      | sK4(X0,X1,X2,X3) != X5
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ r2_hidden(sK4(X0,X1,X2,X3),X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f192,plain,
    ( ~ spl9_1
    | ~ spl9_3
    | spl9_12 ),
    inference(avatar_split_clause,[],[f159,f190,f171,f165])).

fof(f159,plain,(
    ! [X4] :
      ( k1_funct_2(sK0,sK1) != X4
      | r1_partfun1(k3_partfun1(k1_xboole_0,sK0,sK1),sK5(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X4))
      | r2_hidden(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X4),X4)
      | ~ m1_subset_1(k3_partfun1(k1_xboole_0,sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(k3_partfun1(k1_xboole_0,sK0,sK1)) ) ),
    inference(superposition,[],[f91,f136])).

fof(f136,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_partfun1(X0,X1,X2) = X3
      | r1_partfun1(X2,sK5(X0,X1,X2,X3))
      | r2_hidden(sK4(X0,X1,X2,X3),X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f188,plain,
    ( ~ spl9_1
    | ~ spl9_3
    | spl9_10 ),
    inference(avatar_split_clause,[],[f158,f186,f171,f165])).

fof(f158,plain,(
    ! [X3] :
      ( k1_funct_2(sK0,sK1) != X3
      | v1_partfun1(sK5(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X3),sK0)
      | r2_hidden(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X3),X3)
      | ~ m1_subset_1(k3_partfun1(k1_xboole_0,sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(k3_partfun1(k1_xboole_0,sK0,sK1)) ) ),
    inference(superposition,[],[f91,f135])).

fof(f135,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_partfun1(X0,X1,X2) = X3
      | v1_partfun1(sK5(X0,X1,X2,X3),X0)
      | r2_hidden(sK4(X0,X1,X2,X3),X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f184,plain,
    ( ~ spl9_1
    | ~ spl9_3
    | spl9_8 ),
    inference(avatar_split_clause,[],[f157,f182,f171,f165])).

fof(f157,plain,(
    ! [X2] :
      ( k1_funct_2(sK0,sK1) != X2
      | sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X2) = sK5(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X2)
      | r2_hidden(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X2),X2)
      | ~ m1_subset_1(k3_partfun1(k1_xboole_0,sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(k3_partfun1(k1_xboole_0,sK0,sK1)) ) ),
    inference(superposition,[],[f91,f134])).

fof(f134,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_partfun1(X0,X1,X2) = X3
      | sK4(X0,X1,X2,X3) = sK5(X0,X1,X2,X3)
      | r2_hidden(sK4(X0,X1,X2,X3),X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f180,plain,
    ( ~ spl9_1
    | ~ spl9_3
    | spl9_6 ),
    inference(avatar_split_clause,[],[f156,f178,f171,f165])).

fof(f156,plain,(
    ! [X1] :
      ( k1_funct_2(sK0,sK1) != X1
      | m1_subset_1(sK5(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | r2_hidden(sK4(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1),X1),X1)
      | ~ m1_subset_1(k3_partfun1(k1_xboole_0,sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(k3_partfun1(k1_xboole_0,sK0,sK1)) ) ),
    inference(superposition,[],[f91,f133])).

fof(f133,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_partfun1(X0,X1,X2) = X3
      | m1_subset_1(sK5(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK4(X0,X1,X2,X3),X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f90])).
%------------------------------------------------------------------------------
