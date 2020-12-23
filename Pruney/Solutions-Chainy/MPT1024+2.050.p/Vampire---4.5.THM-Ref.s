%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:19 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 300 expanded)
%              Number of leaves         :   43 ( 139 expanded)
%              Depth                    :   10
%              Number of atoms          :  597 (1297 expanded)
%              Number of equality atoms :  118 ( 293 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f974,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f83,f87,f91,f107,f118,f132,f135,f145,f160,f171,f176,f183,f305,f313,f328,f340,f400,f476,f610,f785,f827,f828,f868,f884,f972,f973])).

fof(f973,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | k1_xboole_0 != sK0
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f972,plain,
    ( spl9_153
    | ~ spl9_132
    | ~ spl9_131 ),
    inference(avatar_split_clause,[],[f963,f866,f871,f969])).

fof(f969,plain,
    ( spl9_153
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_153])])).

fof(f871,plain,
    ( spl9_132
  <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_132])])).

fof(f866,plain,
    ( spl9_131
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_131])])).

fof(f963,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl9_131 ),
    inference(resolution,[],[f867,f75])).

fof(f75,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f21])).

% (30476)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f867,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl9_131 ),
    inference(avatar_component_clause,[],[f866])).

fof(f884,plain,
    ( spl9_132
    | ~ spl9_47
    | ~ spl9_49 ),
    inference(avatar_split_clause,[],[f839,f337,f326,f871])).

fof(f326,plain,
    ( spl9_47
  <=> v1_funct_2(sK3,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_47])])).

fof(f337,plain,
    ( spl9_49
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).

fof(f839,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl9_47
    | ~ spl9_49 ),
    inference(superposition,[],[f327,f338])).

fof(f338,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_49 ),
    inference(avatar_component_clause,[],[f337])).

fof(f327,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl9_47 ),
    inference(avatar_component_clause,[],[f326])).

fof(f868,plain,
    ( spl9_131
    | ~ spl9_2
    | ~ spl9_44
    | ~ spl9_49 ),
    inference(avatar_split_clause,[],[f864,f337,f302,f81,f866])).

fof(f81,plain,
    ( spl9_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f302,plain,
    ( spl9_44
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_44])])).

fof(f864,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl9_2
    | ~ spl9_44
    | ~ spl9_49 ),
    inference(forward_demodulation,[],[f834,f303])).

fof(f303,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_44 ),
    inference(avatar_component_clause,[],[f302])).

fof(f834,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl9_2
    | ~ spl9_49 ),
    inference(superposition,[],[f82,f338])).

fof(f82,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f828,plain,
    ( ~ spl9_93
    | ~ spl9_88 ),
    inference(avatar_split_clause,[],[f783,f608,f628])).

fof(f628,plain,
    ( spl9_93
  <=> r1_tarski(k1_xboole_0,k4_tarski(sK8(sK4,sK2,k1_xboole_0),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_93])])).

fof(f608,plain,
    ( spl9_88
  <=> r2_hidden(k4_tarski(sK8(sK4,sK2,k1_xboole_0),sK4),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_88])])).

fof(f783,plain,
    ( ~ r1_tarski(k1_xboole_0,k4_tarski(sK8(sK4,sK2,k1_xboole_0),sK4))
    | ~ spl9_88 ),
    inference(resolution,[],[f609,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f609,plain,
    ( r2_hidden(k4_tarski(sK8(sK4,sK2,k1_xboole_0),sK4),k1_xboole_0)
    | ~ spl9_88 ),
    inference(avatar_component_clause,[],[f608])).

fof(f827,plain,
    ( spl9_46
    | ~ spl9_2
    | ~ spl9_44 ),
    inference(avatar_split_clause,[],[f317,f302,f81,f322])).

fof(f322,plain,
    ( spl9_46
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).

fof(f317,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl9_2
    | ~ spl9_44 ),
    inference(superposition,[],[f82,f303])).

fof(f785,plain,(
    spl9_93 ),
    inference(avatar_contradiction_clause,[],[f784])).

fof(f784,plain,
    ( $false
    | spl9_93 ),
    inference(resolution,[],[f629,f42])).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f629,plain,
    ( ~ r1_tarski(k1_xboole_0,k4_tarski(sK8(sK4,sK2,k1_xboole_0),sK4))
    | spl9_93 ),
    inference(avatar_component_clause,[],[f628])).

fof(f610,plain,
    ( spl9_88
    | ~ spl9_9
    | ~ spl9_48 ),
    inference(avatar_split_clause,[],[f549,f334,f116,f608])).

fof(f116,plain,
    ( spl9_9
  <=> r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f334,plain,
    ( spl9_48
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).

fof(f549,plain,
    ( r2_hidden(k4_tarski(sK8(sK4,sK2,k1_xboole_0),sK4),k1_xboole_0)
    | ~ spl9_9
    | ~ spl9_48 ),
    inference(superposition,[],[f117,f335])).

fof(f335,plain,
    ( k1_xboole_0 = sK3
    | ~ spl9_48 ),
    inference(avatar_component_clause,[],[f334])).

fof(f117,plain,
    ( r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3)
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f116])).

fof(f476,plain,
    ( ~ spl9_7
    | spl9_21
    | ~ spl9_61 ),
    inference(avatar_split_clause,[],[f473,f398,f180,f105])).

fof(f105,plain,
    ( spl9_7
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f180,plain,
    ( spl9_21
  <=> r2_hidden(sK7(sK3,sK2,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f398,plain,
    ( spl9_61
  <=> ! [X5,X4] :
        ( r2_hidden(sK7(sK3,X4,X5),sK0)
        | ~ r2_hidden(X5,k9_relat_1(sK3,X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_61])])).

fof(f473,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | spl9_21
    | ~ spl9_61 ),
    inference(resolution,[],[f399,f181])).

fof(f181,plain,
    ( ~ r2_hidden(sK7(sK3,sK2,sK4),sK0)
    | spl9_21 ),
    inference(avatar_component_clause,[],[f180])).

fof(f399,plain,
    ( ! [X4,X5] :
        ( r2_hidden(sK7(sK3,X4,X5),sK0)
        | ~ r2_hidden(X5,k9_relat_1(sK3,X4)) )
    | ~ spl9_61 ),
    inference(avatar_component_clause,[],[f398])).

fof(f400,plain,
    ( ~ spl9_8
    | ~ spl9_4
    | spl9_61
    | ~ spl9_45 ),
    inference(avatar_split_clause,[],[f360,f310,f398,f89,f113])).

fof(f113,plain,
    ( spl9_8
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f89,plain,
    ( spl9_4
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f310,plain,
    ( spl9_45
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_45])])).

fof(f360,plain,
    ( ! [X4,X5] :
        ( r2_hidden(sK7(sK3,X4,X5),sK0)
        | ~ r2_hidden(X5,k9_relat_1(sK3,X4))
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl9_45 ),
    inference(superposition,[],[f70,f311])).

fof(f311,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl9_45 ),
    inference(avatar_component_clause,[],[f310])).

fof(f70,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK5(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK5(X0,X1,X2),X2) )
              & ( ( sK5(X0,X1,X2) = k1_funct_1(X0,sK6(X0,X1,X2))
                  & r2_hidden(sK6(X0,X1,X2),X1)
                  & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK7(X0,X1,X6)) = X6
                    & r2_hidden(sK7(X0,X1,X6),X1)
                    & r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f27,f30,f29,f28])).

fof(f28,plain,(
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
              ( k1_funct_1(X0,X4) != sK5(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK5(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = sK5(X0,X1,X2)
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( sK5(X0,X1,X2) = k1_funct_1(X0,sK6(X0,X1,X2))
        & r2_hidden(sK6(X0,X1,X2),X1)
        & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK7(X0,X1,X6)) = X6
        & r2_hidden(sK7(X0,X1,X6),X1)
        & r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

fof(f340,plain,
    ( spl9_48
    | spl9_49
    | ~ spl9_47
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f330,f322,f326,f337,f334])).

fof(f330,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ spl9_46 ),
    inference(resolution,[],[f323,f73])).

fof(f73,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f323,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl9_46 ),
    inference(avatar_component_clause,[],[f322])).

fof(f328,plain,
    ( spl9_47
    | ~ spl9_3
    | ~ spl9_44 ),
    inference(avatar_split_clause,[],[f318,f302,f85,f326])).

fof(f85,plain,
    ( spl9_3
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f318,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl9_3
    | ~ spl9_44 ),
    inference(superposition,[],[f86,f303])).

fof(f86,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f313,plain,
    ( ~ spl9_2
    | spl9_45
    | ~ spl9_43 ),
    inference(avatar_split_clause,[],[f307,f299,f310,f81])).

fof(f299,plain,
    ( spl9_43
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).

fof(f307,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl9_43 ),
    inference(superposition,[],[f58,f300])).

fof(f300,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl9_43 ),
    inference(avatar_component_clause,[],[f299])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f305,plain,
    ( spl9_43
    | spl9_44
    | ~ spl9_3
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f297,f81,f85,f302,f299])).

fof(f297,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl9_2 ),
    inference(resolution,[],[f59,f82])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f183,plain,
    ( ~ spl9_21
    | ~ spl9_17
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f178,f174,f158,f180])).

fof(f158,plain,
    ( spl9_17
  <=> r2_hidden(sK7(sK3,sK2,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f174,plain,
    ( spl9_20
  <=> sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f178,plain,
    ( ~ r2_hidden(sK7(sK3,sK2,sK4),sK2)
    | ~ r2_hidden(sK7(sK3,sK2,sK4),sK0)
    | ~ spl9_20 ),
    inference(trivial_inequality_removal,[],[f177])).

fof(f177,plain,
    ( sK4 != sK4
    | ~ r2_hidden(sK7(sK3,sK2,sK4),sK2)
    | ~ r2_hidden(sK7(sK3,sK2,sK4),sK0)
    | ~ spl9_20 ),
    inference(superposition,[],[f41,f175])).

fof(f175,plain,
    ( sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4))
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f174])).

fof(f41,plain,(
    ! [X5] :
      ( k1_funct_1(sK3,X5) != sK4
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X5,sK0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ! [X5] :
        ( k1_funct_1(sK3,X5) != sK4
        | ~ r2_hidden(X5,sK2)
        | ~ r2_hidden(X5,sK0) )
    & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f13,f24,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK3,X5) != X4
              | ~ r2_hidden(X5,sK2)
              | ~ r2_hidden(X5,sK0) )
          & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X4] :
        ( ! [X5] :
            ( k1_funct_1(sK3,X5) != X4
            | ~ r2_hidden(X5,sK2)
            | ~ r2_hidden(X5,sK0) )
        & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) )
   => ( ! [X5] :
          ( k1_funct_1(sK3,X5) != sK4
          | ~ r2_hidden(X5,sK2)
          | ~ r2_hidden(X5,sK0) )
      & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f176,plain,
    ( spl9_20
    | ~ spl9_7
    | ~ spl9_19 ),
    inference(avatar_split_clause,[],[f172,f169,f105,f174])).

fof(f169,plain,
    ( spl9_19
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | k1_funct_1(sK3,sK7(sK3,X1,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f172,plain,
    ( sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4))
    | ~ spl9_7
    | ~ spl9_19 ),
    inference(resolution,[],[f170,f106])).

fof(f106,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f105])).

fof(f170,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | k1_funct_1(sK3,sK7(sK3,X1,X0)) = X0 )
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f169])).

fof(f171,plain,
    ( ~ spl9_8
    | spl9_19
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f167,f89,f169,f113])).

fof(f167,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | k1_funct_1(sK3,sK7(sK3,X1,X0)) = X0
        | ~ v1_relat_1(sK3) )
    | ~ spl9_4 ),
    inference(resolution,[],[f68,f90])).

fof(f90,plain,
    ( v1_funct_1(sK3)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f68,plain,(
    ! [X6,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | k1_funct_1(X0,sK7(X0,X1,X6)) = X6
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK7(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f160,plain,
    ( spl9_17
    | ~ spl9_7
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f156,f143,f105,f158])).

fof(f143,plain,
    ( spl9_14
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | r2_hidden(sK7(sK3,X1,X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f156,plain,
    ( r2_hidden(sK7(sK3,sK2,sK4),sK2)
    | ~ spl9_7
    | ~ spl9_14 ),
    inference(resolution,[],[f144,f106])).

fof(f144,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | r2_hidden(sK7(sK3,X1,X0),X1) )
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f143])).

fof(f145,plain,
    ( ~ spl9_8
    | spl9_14
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f141,f89,f143,f113])).

fof(f141,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | r2_hidden(sK7(sK3,X1,X0),X1)
        | ~ v1_relat_1(sK3) )
    | ~ spl9_4 ),
    inference(resolution,[],[f69,f90])).

fof(f69,plain,(
    ! [X6,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | r2_hidden(sK7(X0,X1,X6),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f135,plain,(
    spl9_12 ),
    inference(avatar_contradiction_clause,[],[f133])).

fof(f133,plain,
    ( $false
    | spl9_12 ),
    inference(resolution,[],[f131,f52])).

fof(f52,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f131,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl9_12 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl9_12
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f132,plain,
    ( ~ spl9_12
    | ~ spl9_2
    | spl9_8 ),
    inference(avatar_split_clause,[],[f128,f113,f81,f130])).

fof(f128,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl9_2
    | spl9_8 ),
    inference(resolution,[],[f127,f82])).

fof(f127,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl9_8 ),
    inference(resolution,[],[f114,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f114,plain,
    ( ~ v1_relat_1(sK3)
    | spl9_8 ),
    inference(avatar_component_clause,[],[f113])).

fof(f118,plain,
    ( ~ spl9_8
    | spl9_9
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f108,f105,f116,f113])).

fof(f108,plain,
    ( r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl9_7 ),
    inference(resolution,[],[f106,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK8(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2)
            & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f33,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK8(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2)
        & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f107,plain,
    ( spl9_7
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f99,f81,f77,f105])).

fof(f77,plain,
    ( spl9_1
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f99,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(superposition,[],[f78,f97])).

fof(f97,plain,
    ( ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)
    | ~ spl9_2 ),
    inference(resolution,[],[f65,f82])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f78,plain,
    ( r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f91,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f37,f89])).

fof(f37,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f87,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f38,f85])).

fof(f38,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f83,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f39,f81])).

fof(f39,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f79,plain,(
    spl9_1 ),
    inference(avatar_split_clause,[],[f40,f77])).

fof(f40,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:11:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (30478)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % (30473)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (30473)Refutation not found, incomplete strategy% (30473)------------------------------
% 0.22/0.48  % (30473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (30473)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (30473)Memory used [KB]: 10618
% 0.22/0.48  % (30473)Time elapsed: 0.060 s
% 0.22/0.48  % (30473)------------------------------
% 0.22/0.48  % (30473)------------------------------
% 0.22/0.49  % (30486)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (30485)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  % (30481)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  % (30480)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.50  % (30478)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f974,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f79,f83,f87,f91,f107,f118,f132,f135,f145,f160,f171,f176,f183,f305,f313,f328,f340,f400,f476,f610,f785,f827,f828,f868,f884,f972,f973])).
% 0.22/0.50  fof(f973,plain,(
% 0.22/0.50    k1_xboole_0 != sK1 | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | k1_xboole_0 != sK0 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.22/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.50  fof(f972,plain,(
% 0.22/0.50    spl9_153 | ~spl9_132 | ~spl9_131),
% 0.22/0.50    inference(avatar_split_clause,[],[f963,f866,f871,f969])).
% 0.22/0.50  fof(f969,plain,(
% 0.22/0.50    spl9_153 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_153])])).
% 0.22/0.50  fof(f871,plain,(
% 0.22/0.50    spl9_132 <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_132])])).
% 0.22/0.50  fof(f866,plain,(
% 0.22/0.50    spl9_131 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_131])])).
% 0.22/0.50  fof(f963,plain,(
% 0.22/0.50    ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | ~spl9_131),
% 0.22/0.50    inference(resolution,[],[f867,f75])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)) )),
% 0.22/0.50    inference(equality_resolution,[],[f60])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(nnf_transformation,[],[f21])).
% 0.22/0.50  % (30476)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(flattening,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.50  fof(f867,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl9_131),
% 0.22/0.50    inference(avatar_component_clause,[],[f866])).
% 0.22/0.50  fof(f884,plain,(
% 0.22/0.50    spl9_132 | ~spl9_47 | ~spl9_49),
% 0.22/0.50    inference(avatar_split_clause,[],[f839,f337,f326,f871])).
% 0.22/0.50  fof(f326,plain,(
% 0.22/0.50    spl9_47 <=> v1_funct_2(sK3,sK0,k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_47])])).
% 0.22/0.50  fof(f337,plain,(
% 0.22/0.50    spl9_49 <=> k1_xboole_0 = sK0),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).
% 0.22/0.50  fof(f839,plain,(
% 0.22/0.50    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl9_47 | ~spl9_49)),
% 0.22/0.50    inference(superposition,[],[f327,f338])).
% 0.22/0.50  fof(f338,plain,(
% 0.22/0.50    k1_xboole_0 = sK0 | ~spl9_49),
% 0.22/0.50    inference(avatar_component_clause,[],[f337])).
% 0.22/0.50  fof(f327,plain,(
% 0.22/0.50    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl9_47),
% 0.22/0.50    inference(avatar_component_clause,[],[f326])).
% 0.22/0.50  fof(f868,plain,(
% 0.22/0.50    spl9_131 | ~spl9_2 | ~spl9_44 | ~spl9_49),
% 0.22/0.50    inference(avatar_split_clause,[],[f864,f337,f302,f81,f866])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    spl9_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.22/0.50  fof(f302,plain,(
% 0.22/0.50    spl9_44 <=> k1_xboole_0 = sK1),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_44])])).
% 0.22/0.50  fof(f864,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl9_2 | ~spl9_44 | ~spl9_49)),
% 0.22/0.50    inference(forward_demodulation,[],[f834,f303])).
% 0.22/0.50  fof(f303,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | ~spl9_44),
% 0.22/0.50    inference(avatar_component_clause,[],[f302])).
% 0.22/0.50  fof(f834,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl9_2 | ~spl9_49)),
% 0.22/0.50    inference(superposition,[],[f82,f338])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl9_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f81])).
% 0.22/0.50  fof(f828,plain,(
% 0.22/0.50    ~spl9_93 | ~spl9_88),
% 0.22/0.50    inference(avatar_split_clause,[],[f783,f608,f628])).
% 0.22/0.50  fof(f628,plain,(
% 0.22/0.50    spl9_93 <=> r1_tarski(k1_xboole_0,k4_tarski(sK8(sK4,sK2,k1_xboole_0),sK4))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_93])])).
% 0.22/0.50  fof(f608,plain,(
% 0.22/0.50    spl9_88 <=> r2_hidden(k4_tarski(sK8(sK4,sK2,k1_xboole_0),sK4),k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_88])])).
% 0.22/0.50  fof(f783,plain,(
% 0.22/0.50    ~r1_tarski(k1_xboole_0,k4_tarski(sK8(sK4,sK2,k1_xboole_0),sK4)) | ~spl9_88),
% 0.22/0.50    inference(resolution,[],[f609,f53])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.50  fof(f609,plain,(
% 0.22/0.50    r2_hidden(k4_tarski(sK8(sK4,sK2,k1_xboole_0),sK4),k1_xboole_0) | ~spl9_88),
% 0.22/0.50    inference(avatar_component_clause,[],[f608])).
% 0.22/0.50  fof(f827,plain,(
% 0.22/0.50    spl9_46 | ~spl9_2 | ~spl9_44),
% 0.22/0.50    inference(avatar_split_clause,[],[f317,f302,f81,f322])).
% 0.22/0.50  fof(f322,plain,(
% 0.22/0.50    spl9_46 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).
% 0.22/0.50  fof(f317,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl9_2 | ~spl9_44)),
% 0.22/0.50    inference(superposition,[],[f82,f303])).
% 0.22/0.50  fof(f785,plain,(
% 0.22/0.50    spl9_93),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f784])).
% 0.22/0.50  fof(f784,plain,(
% 0.22/0.50    $false | spl9_93),
% 0.22/0.50    inference(resolution,[],[f629,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.50  fof(f629,plain,(
% 0.22/0.50    ~r1_tarski(k1_xboole_0,k4_tarski(sK8(sK4,sK2,k1_xboole_0),sK4)) | spl9_93),
% 0.22/0.50    inference(avatar_component_clause,[],[f628])).
% 0.22/0.50  fof(f610,plain,(
% 0.22/0.50    spl9_88 | ~spl9_9 | ~spl9_48),
% 0.22/0.50    inference(avatar_split_clause,[],[f549,f334,f116,f608])).
% 0.22/0.50  fof(f116,plain,(
% 0.22/0.50    spl9_9 <=> r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.22/0.50  fof(f334,plain,(
% 0.22/0.50    spl9_48 <=> k1_xboole_0 = sK3),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).
% 0.22/0.50  fof(f549,plain,(
% 0.22/0.50    r2_hidden(k4_tarski(sK8(sK4,sK2,k1_xboole_0),sK4),k1_xboole_0) | (~spl9_9 | ~spl9_48)),
% 0.22/0.50    inference(superposition,[],[f117,f335])).
% 0.22/0.50  fof(f335,plain,(
% 0.22/0.50    k1_xboole_0 = sK3 | ~spl9_48),
% 0.22/0.50    inference(avatar_component_clause,[],[f334])).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3) | ~spl9_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f116])).
% 0.22/0.50  fof(f476,plain,(
% 0.22/0.50    ~spl9_7 | spl9_21 | ~spl9_61),
% 0.22/0.50    inference(avatar_split_clause,[],[f473,f398,f180,f105])).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    spl9_7 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.22/0.50  fof(f180,plain,(
% 0.22/0.50    spl9_21 <=> r2_hidden(sK7(sK3,sK2,sK4),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 0.22/0.50  fof(f398,plain,(
% 0.22/0.50    spl9_61 <=> ! [X5,X4] : (r2_hidden(sK7(sK3,X4,X5),sK0) | ~r2_hidden(X5,k9_relat_1(sK3,X4)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_61])])).
% 0.22/0.50  fof(f473,plain,(
% 0.22/0.50    ~r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (spl9_21 | ~spl9_61)),
% 0.22/0.50    inference(resolution,[],[f399,f181])).
% 0.22/0.50  fof(f181,plain,(
% 0.22/0.50    ~r2_hidden(sK7(sK3,sK2,sK4),sK0) | spl9_21),
% 0.22/0.50    inference(avatar_component_clause,[],[f180])).
% 0.22/0.50  fof(f399,plain,(
% 0.22/0.50    ( ! [X4,X5] : (r2_hidden(sK7(sK3,X4,X5),sK0) | ~r2_hidden(X5,k9_relat_1(sK3,X4))) ) | ~spl9_61),
% 0.22/0.50    inference(avatar_component_clause,[],[f398])).
% 0.22/0.50  fof(f400,plain,(
% 0.22/0.50    ~spl9_8 | ~spl9_4 | spl9_61 | ~spl9_45),
% 0.22/0.50    inference(avatar_split_clause,[],[f360,f310,f398,f89,f113])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    spl9_8 <=> v1_relat_1(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    spl9_4 <=> v1_funct_1(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.22/0.50  fof(f310,plain,(
% 0.22/0.50    spl9_45 <=> sK0 = k1_relat_1(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_45])])).
% 0.22/0.50  fof(f360,plain,(
% 0.22/0.50    ( ! [X4,X5] : (r2_hidden(sK7(sK3,X4,X5),sK0) | ~r2_hidden(X5,k9_relat_1(sK3,X4)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) ) | ~spl9_45),
% 0.22/0.50    inference(superposition,[],[f70,f311])).
% 0.22/0.50  fof(f311,plain,(
% 0.22/0.50    sK0 = k1_relat_1(sK3) | ~spl9_45),
% 0.22/0.50    inference(avatar_component_clause,[],[f310])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    ( ! [X6,X0,X1] : (r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(equality_resolution,[],[f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X6,X2,X0,X1] : (r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK5(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((sK5(X0,X1,X2) = k1_funct_1(X0,sK6(X0,X1,X2)) & r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK7(X0,X1,X6)) = X6 & r2_hidden(sK7(X0,X1,X6),X1) & r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f27,f30,f29,f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK5(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK5(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = sK5(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (sK5(X0,X1,X2) = k1_funct_1(X0,sK6(X0,X1,X2)) & r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK7(X0,X1,X6)) = X6 & r2_hidden(sK7(X0,X1,X6),X1) & r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(rectify,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).
% 0.22/0.50  fof(f340,plain,(
% 0.22/0.50    spl9_48 | spl9_49 | ~spl9_47 | ~spl9_46),
% 0.22/0.50    inference(avatar_split_clause,[],[f330,f322,f326,f337,f334])).
% 0.22/0.50  fof(f330,plain,(
% 0.22/0.50    ~v1_funct_2(sK3,sK0,k1_xboole_0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | ~spl9_46),
% 0.22/0.50    inference(resolution,[],[f323,f73])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2) )),
% 0.22/0.50    inference(equality_resolution,[],[f63])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f36])).
% 0.22/0.50  fof(f323,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl9_46),
% 0.22/0.50    inference(avatar_component_clause,[],[f322])).
% 0.22/0.50  fof(f328,plain,(
% 0.22/0.50    spl9_47 | ~spl9_3 | ~spl9_44),
% 0.22/0.50    inference(avatar_split_clause,[],[f318,f302,f85,f326])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    spl9_3 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.22/0.50  fof(f318,plain,(
% 0.22/0.50    v1_funct_2(sK3,sK0,k1_xboole_0) | (~spl9_3 | ~spl9_44)),
% 0.22/0.50    inference(superposition,[],[f86,f303])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    v1_funct_2(sK3,sK0,sK1) | ~spl9_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f85])).
% 0.22/0.50  fof(f313,plain,(
% 0.22/0.50    ~spl9_2 | spl9_45 | ~spl9_43),
% 0.22/0.50    inference(avatar_split_clause,[],[f307,f299,f310,f81])).
% 0.22/0.50  fof(f299,plain,(
% 0.22/0.50    spl9_43 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).
% 0.22/0.50  fof(f307,plain,(
% 0.22/0.50    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl9_43),
% 0.22/0.50    inference(superposition,[],[f58,f300])).
% 0.22/0.50  fof(f300,plain,(
% 0.22/0.50    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl9_43),
% 0.22/0.50    inference(avatar_component_clause,[],[f299])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.50  fof(f305,plain,(
% 0.22/0.50    spl9_43 | spl9_44 | ~spl9_3 | ~spl9_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f297,f81,f85,f302,f299])).
% 0.22/0.50  fof(f297,plain,(
% 0.22/0.50    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl9_2),
% 0.22/0.50    inference(resolution,[],[f59,f82])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f36])).
% 0.22/0.50  fof(f183,plain,(
% 0.22/0.50    ~spl9_21 | ~spl9_17 | ~spl9_20),
% 0.22/0.50    inference(avatar_split_clause,[],[f178,f174,f158,f180])).
% 0.22/0.50  fof(f158,plain,(
% 0.22/0.50    spl9_17 <=> r2_hidden(sK7(sK3,sK2,sK4),sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 0.22/0.50  fof(f174,plain,(
% 0.22/0.50    spl9_20 <=> sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).
% 0.22/0.50  fof(f178,plain,(
% 0.22/0.50    ~r2_hidden(sK7(sK3,sK2,sK4),sK2) | ~r2_hidden(sK7(sK3,sK2,sK4),sK0) | ~spl9_20),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f177])).
% 0.22/0.50  fof(f177,plain,(
% 0.22/0.50    sK4 != sK4 | ~r2_hidden(sK7(sK3,sK2,sK4),sK2) | ~r2_hidden(sK7(sK3,sK2,sK4),sK0) | ~spl9_20),
% 0.22/0.50    inference(superposition,[],[f41,f175])).
% 0.22/0.50  fof(f175,plain,(
% 0.22/0.50    sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4)) | ~spl9_20),
% 0.22/0.50    inference(avatar_component_clause,[],[f174])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    (! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0)) & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f13,f24,f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0)) & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ? [X4] : (! [X5] : (k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0)) & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))) => (! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0)) & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.22/0.50    inference(flattening,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.22/0.50    inference(negated_conjecture,[],[f10])).
% 0.22/0.50  fof(f10,conjecture,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).
% 0.22/0.50  fof(f176,plain,(
% 0.22/0.50    spl9_20 | ~spl9_7 | ~spl9_19),
% 0.22/0.50    inference(avatar_split_clause,[],[f172,f169,f105,f174])).
% 0.22/0.50  fof(f169,plain,(
% 0.22/0.50    spl9_19 <=> ! [X1,X0] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | k1_funct_1(sK3,sK7(sK3,X1,X0)) = X0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 0.22/0.50  fof(f172,plain,(
% 0.22/0.50    sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4)) | (~spl9_7 | ~spl9_19)),
% 0.22/0.50    inference(resolution,[],[f170,f106])).
% 0.22/0.50  fof(f106,plain,(
% 0.22/0.50    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~spl9_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f105])).
% 0.22/0.50  fof(f170,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | k1_funct_1(sK3,sK7(sK3,X1,X0)) = X0) ) | ~spl9_19),
% 0.22/0.50    inference(avatar_component_clause,[],[f169])).
% 0.22/0.50  fof(f171,plain,(
% 0.22/0.50    ~spl9_8 | spl9_19 | ~spl9_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f167,f89,f169,f113])).
% 0.22/0.50  fof(f167,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | k1_funct_1(sK3,sK7(sK3,X1,X0)) = X0 | ~v1_relat_1(sK3)) ) | ~spl9_4),
% 0.22/0.50    inference(resolution,[],[f68,f90])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    v1_funct_1(sK3) | ~spl9_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f89])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    ( ! [X6,X0,X1] : (~v1_funct_1(X0) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | k1_funct_1(X0,sK7(X0,X1,X6)) = X6 | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(equality_resolution,[],[f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X6,X2,X0,X1] : (k1_funct_1(X0,sK7(X0,X1,X6)) = X6 | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f160,plain,(
% 0.22/0.50    spl9_17 | ~spl9_7 | ~spl9_14),
% 0.22/0.50    inference(avatar_split_clause,[],[f156,f143,f105,f158])).
% 0.22/0.50  fof(f143,plain,(
% 0.22/0.50    spl9_14 <=> ! [X1,X0] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | r2_hidden(sK7(sK3,X1,X0),X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 0.22/0.50  fof(f156,plain,(
% 0.22/0.50    r2_hidden(sK7(sK3,sK2,sK4),sK2) | (~spl9_7 | ~spl9_14)),
% 0.22/0.50    inference(resolution,[],[f144,f106])).
% 0.22/0.50  fof(f144,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | r2_hidden(sK7(sK3,X1,X0),X1)) ) | ~spl9_14),
% 0.22/0.50    inference(avatar_component_clause,[],[f143])).
% 0.22/0.50  fof(f145,plain,(
% 0.22/0.50    ~spl9_8 | spl9_14 | ~spl9_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f141,f89,f143,f113])).
% 0.22/0.50  fof(f141,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | r2_hidden(sK7(sK3,X1,X0),X1) | ~v1_relat_1(sK3)) ) | ~spl9_4),
% 0.22/0.50    inference(resolution,[],[f69,f90])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    ( ! [X6,X0,X1] : (~v1_funct_1(X0) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | r2_hidden(sK7(X0,X1,X6),X1) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(equality_resolution,[],[f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X6,X2,X0,X1] : (r2_hidden(sK7(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f135,plain,(
% 0.22/0.50    spl9_12),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f133])).
% 0.22/0.50  fof(f133,plain,(
% 0.22/0.50    $false | spl9_12),
% 0.22/0.50    inference(resolution,[],[f131,f52])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.50  fof(f131,plain,(
% 0.22/0.50    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl9_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f130])).
% 0.22/0.50  fof(f130,plain,(
% 0.22/0.50    spl9_12 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 0.22/0.50  fof(f132,plain,(
% 0.22/0.50    ~spl9_12 | ~spl9_2 | spl9_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f128,f113,f81,f130])).
% 0.22/0.50  fof(f128,plain,(
% 0.22/0.50    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | (~spl9_2 | spl9_8)),
% 0.22/0.50    inference(resolution,[],[f127,f82])).
% 0.22/0.50  fof(f127,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl9_8),
% 0.22/0.50    inference(resolution,[],[f114,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.50  fof(f114,plain,(
% 0.22/0.50    ~v1_relat_1(sK3) | spl9_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f113])).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    ~spl9_8 | spl9_9 | ~spl9_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f108,f105,f116,f113])).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3) | ~v1_relat_1(sK3) | ~spl9_7),
% 0.22/0.50    inference(resolution,[],[f106,f55])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2) | ~v1_relat_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2) & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f33,f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2) & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.50    inference(rectify,[],[f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.50    inference(nnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    spl9_7 | ~spl9_1 | ~spl9_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f99,f81,f77,f105])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    spl9_1 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl9_1 | ~spl9_2)),
% 0.22/0.50    inference(superposition,[],[f78,f97])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    ( ! [X0] : (k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)) ) | ~spl9_2),
% 0.22/0.50    inference(resolution,[],[f65,f82])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | ~spl9_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f77])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    spl9_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f37,f89])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    v1_funct_1(sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    spl9_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f38,f85])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    spl9_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f39,f81])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    spl9_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f40,f77])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (30478)------------------------------
% 0.22/0.50  % (30478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (30478)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (30478)Memory used [KB]: 11385
% 0.22/0.50  % (30478)Time elapsed: 0.075 s
% 0.22/0.50  % (30478)------------------------------
% 0.22/0.50  % (30478)------------------------------
% 0.22/0.51  % (30471)Success in time 0.139 s
%------------------------------------------------------------------------------
