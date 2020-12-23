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
% DateTime   : Thu Dec  3 13:02:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  266 ( 592 expanded)
%              Number of leaves         :   59 ( 253 expanded)
%              Depth                    :   14
%              Number of atoms          :  977 (4128 expanded)
%              Number of equality atoms :  247 (1483 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1313,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f117,f122,f127,f132,f137,f142,f147,f152,f157,f162,f182,f184,f190,f196,f202,f272,f273,f382,f390,f426,f431,f502,f506,f594,f609,f720,f742,f743,f744,f763,f773,f826,f828,f901,f960,f961,f975,f1312])).

fof(f1312,plain,
    ( ~ spl16_38
    | ~ spl16_62
    | ~ spl16_63 ),
    inference(avatar_contradiction_clause,[],[f1311])).

fof(f1311,plain,
    ( $false
    | ~ spl16_38
    | ~ spl16_62
    | ~ spl16_63 ),
    inference(subsumption_resolution,[],[f1310,f719])).

fof(f719,plain,
    ( sP1(sK10,sK11)
    | ~ spl16_38 ),
    inference(avatar_component_clause,[],[f717])).

fof(f717,plain,
    ( spl16_38
  <=> sP1(sK10,sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_38])])).

fof(f1310,plain,
    ( ~ sP1(sK10,sK11)
    | ~ spl16_62
    | ~ spl16_63 ),
    inference(subsumption_resolution,[],[f1302,f959])).

fof(f959,plain,
    ( sK13(sK10,sK11) = k1_funct_1(sK10,sK12(sK10,sK11))
    | ~ spl16_63 ),
    inference(avatar_component_clause,[],[f957])).

fof(f957,plain,
    ( spl16_63
  <=> sK13(sK10,sK11) = k1_funct_1(sK10,sK12(sK10,sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_63])])).

fof(f1302,plain,
    ( sK13(sK10,sK11) != k1_funct_1(sK10,sK12(sK10,sK11))
    | ~ sP1(sK10,sK11)
    | ~ spl16_62 ),
    inference(resolution,[],[f998,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( sP0(sK12(X0,X1),sK13(X0,X1),X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( sP0(sK12(X0,X1),sK13(X0,X1),X1,X0)
        & r2_hidden(sK13(X0,X1),k1_relat_1(X1))
        & r2_hidden(sK12(X0,X1),k1_relat_1(X0)) )
      | ~ sP1(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( sP0(X2,X3,X1,X0)
          & r2_hidden(X3,k1_relat_1(X1))
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( sP0(sK12(X0,X1),sK13(X0,X1),X1,X0)
        & r2_hidden(sK13(X0,X1),k1_relat_1(X1))
        & r2_hidden(sK12(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ? [X2,X3] :
          ( sP0(X2,X3,X1,X0)
          & r2_hidden(X3,k1_relat_1(X1))
          & r2_hidden(X2,k1_relat_1(X0)) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ? [X2,X3] :
          ( sP0(X2,X3,X1,X0)
          & r2_hidden(X3,k1_relat_1(X1))
          & r2_hidden(X2,k1_relat_1(X0)) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f998,plain,
    ( ! [X2] :
        ( ~ sP0(sK12(sK10,sK11),sK13(sK10,sK11),sK11,X2)
        | sK13(sK10,sK11) != k1_funct_1(X2,sK12(sK10,sK11)) )
    | ~ spl16_62 ),
    inference(superposition,[],[f101,f955])).

fof(f955,plain,
    ( sK12(sK10,sK11) = k1_funct_1(sK11,sK13(sK10,sK11))
    | ~ spl16_62 ),
    inference(avatar_component_clause,[],[f953])).

fof(f953,plain,
    ( spl16_62
  <=> sK12(sK10,sK11) = k1_funct_1(sK11,sK13(sK10,sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_62])])).

fof(f101,plain,(
    ! [X2,X3,X1] :
      ( ~ sP0(k1_funct_1(X2,X1),X1,X2,X3)
      | k1_funct_1(X3,k1_funct_1(X2,X1)) != X1 ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X1) != X0
      | k1_funct_1(X3,X0) != X1
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_funct_1(X2,X1) != X0
          | k1_funct_1(X3,X0) != X1 )
        & ( k1_funct_1(X2,X1) = X0
          | k1_funct_1(X3,X0) = X1 ) )
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X2,X3,X1,X0] :
      ( ( ( k1_funct_1(X1,X3) != X2
          | k1_funct_1(X0,X2) != X3 )
        & ( k1_funct_1(X1,X3) = X2
          | k1_funct_1(X0,X2) = X3 ) )
      | ~ sP0(X2,X3,X1,X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X2,X3,X1,X0] :
      ( ( k1_funct_1(X0,X2) = X3
      <~> k1_funct_1(X1,X3) = X2 )
      | ~ sP0(X2,X3,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f975,plain,
    ( spl16_62
    | ~ spl16_44
    | ~ spl16_63 ),
    inference(avatar_split_clause,[],[f967,f957,f760,f953])).

fof(f760,plain,
    ( spl16_44
  <=> sK12(sK10,sK11) = k1_funct_1(sK11,k1_funct_1(sK10,sK12(sK10,sK11))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_44])])).

fof(f967,plain,
    ( sK12(sK10,sK11) = k1_funct_1(sK11,sK13(sK10,sK11))
    | ~ spl16_44
    | ~ spl16_63 ),
    inference(backward_demodulation,[],[f762,f959])).

fof(f762,plain,
    ( sK12(sK10,sK11) = k1_funct_1(sK11,k1_funct_1(sK10,sK12(sK10,sK11)))
    | ~ spl16_44 ),
    inference(avatar_component_clause,[],[f760])).

fof(f961,plain,
    ( sK12(sK10,sK11) != k1_funct_1(sK11,sK13(sK10,sK11))
    | k1_funct_1(sK11,sK13(sK10,sK11)) != sK15(sK13(sK10,sK11),sK10)
    | sK13(sK10,sK11) != k1_funct_1(sK10,sK15(sK13(sK10,sK11),sK10))
    | sK13(sK10,sK11) = k1_funct_1(sK10,sK12(sK10,sK11)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f960,plain,
    ( spl16_62
    | spl16_63
    | ~ spl16_41 ),
    inference(avatar_split_clause,[],[f951,f739,f957,f953])).

fof(f739,plain,
    ( spl16_41
  <=> sP0(sK12(sK10,sK11),sK13(sK10,sK11),sK11,sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_41])])).

fof(f951,plain,
    ( sK13(sK10,sK11) = k1_funct_1(sK10,sK12(sK10,sK11))
    | sK12(sK10,sK11) = k1_funct_1(sK11,sK13(sK10,sK11))
    | ~ spl16_41 ),
    inference(resolution,[],[f741,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | k1_funct_1(X3,X0) = X1
      | k1_funct_1(X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f741,plain,
    ( sP0(sK12(sK10,sK11),sK13(sK10,sK11),sK11,sK10)
    | ~ spl16_41 ),
    inference(avatar_component_clause,[],[f739])).

fof(f901,plain,
    ( spl16_57
    | ~ spl16_50
    | ~ spl16_51 ),
    inference(avatar_split_clause,[],[f896,f823,f818,f898])).

fof(f898,plain,
    ( spl16_57
  <=> k1_funct_1(sK11,sK13(sK10,sK11)) = sK15(sK13(sK10,sK11),sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_57])])).

fof(f818,plain,
    ( spl16_50
  <=> r2_hidden(sK15(sK13(sK10,sK11),sK10),sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_50])])).

fof(f823,plain,
    ( spl16_51
  <=> sK13(sK10,sK11) = k1_funct_1(sK10,sK15(sK13(sK10,sK11),sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_51])])).

fof(f896,plain,
    ( k1_funct_1(sK11,sK13(sK10,sK11)) = sK15(sK13(sK10,sK11),sK10)
    | ~ spl16_50
    | ~ spl16_51 ),
    inference(forward_demodulation,[],[f884,f825])).

fof(f825,plain,
    ( sK13(sK10,sK11) = k1_funct_1(sK10,sK15(sK13(sK10,sK11),sK10))
    | ~ spl16_51 ),
    inference(avatar_component_clause,[],[f823])).

fof(f884,plain,
    ( sK15(sK13(sK10,sK11),sK10) = k1_funct_1(sK11,k1_funct_1(sK10,sK15(sK13(sK10,sK11),sK10)))
    | ~ spl16_50 ),
    inference(unit_resulting_resolution,[],[f820,f97])).

fof(f97,plain,(
    ! [X5] :
      ( k1_funct_1(sK11,k1_funct_1(sK10,X5)) = X5
      | ~ r2_hidden(X5,sK8) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X4,X5] :
      ( k1_funct_1(sK11,X4) = X5
      | k1_funct_1(sK10,X5) != X4
      | ~ r2_hidden(X5,sK8) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( k2_funct_1(sK10) != sK11
    & k1_xboole_0 != sK9
    & k1_xboole_0 != sK8
    & ! [X4,X5] :
        ( ( ( k1_funct_1(sK11,X4) = X5
            & r2_hidden(X4,sK9) )
          | k1_funct_1(sK10,X5) != X4
          | ~ r2_hidden(X5,sK8) )
        & ( ( k1_funct_1(sK10,X5) = X4
            & r2_hidden(X5,sK8) )
          | k1_funct_1(sK11,X4) != X5
          | ~ r2_hidden(X4,sK9) ) )
    & v2_funct_1(sK10)
    & sK9 = k2_relset_1(sK8,sK9,sK10)
    & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK8)))
    & v1_funct_2(sK11,sK9,sK8)
    & v1_funct_1(sK11)
    & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
    & v1_funct_2(sK10,sK8,sK9)
    & v1_funct_1(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f11,f33,f32])).

% (13558)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & ! [X4,X5] :
                ( ( ( k1_funct_1(X3,X4) = X5
                    & r2_hidden(X4,X1) )
                  | k1_funct_1(X2,X5) != X4
                  | ~ r2_hidden(X5,X0) )
                & ( ( k1_funct_1(X2,X5) = X4
                    & r2_hidden(X5,X0) )
                  | k1_funct_1(X3,X4) != X5
                  | ~ r2_hidden(X4,X1) ) )
            & v2_funct_1(X2)
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK10) != X3
          & k1_xboole_0 != sK9
          & k1_xboole_0 != sK8
          & ! [X5,X4] :
              ( ( ( k1_funct_1(X3,X4) = X5
                  & r2_hidden(X4,sK9) )
                | k1_funct_1(sK10,X5) != X4
                | ~ r2_hidden(X5,sK8) )
              & ( ( k1_funct_1(sK10,X5) = X4
                  & r2_hidden(X5,sK8) )
                | k1_funct_1(X3,X4) != X5
                | ~ r2_hidden(X4,sK9) ) )
          & v2_funct_1(sK10)
          & sK9 = k2_relset_1(sK8,sK9,sK10)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK9,sK8)))
          & v1_funct_2(X3,sK9,sK8)
          & v1_funct_1(X3) )
      & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
      & v1_funct_2(sK10,sK8,sK9)
      & v1_funct_1(sK10) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X3] :
        ( k2_funct_1(sK10) != X3
        & k1_xboole_0 != sK9
        & k1_xboole_0 != sK8
        & ! [X5,X4] :
            ( ( ( k1_funct_1(X3,X4) = X5
                & r2_hidden(X4,sK9) )
              | k1_funct_1(sK10,X5) != X4
              | ~ r2_hidden(X5,sK8) )
            & ( ( k1_funct_1(sK10,X5) = X4
                & r2_hidden(X5,sK8) )
              | k1_funct_1(X3,X4) != X5
              | ~ r2_hidden(X4,sK9) ) )
        & v2_funct_1(sK10)
        & sK9 = k2_relset_1(sK8,sK9,sK10)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK9,sK8)))
        & v1_funct_2(X3,sK9,sK8)
        & v1_funct_1(X3) )
   => ( k2_funct_1(sK10) != sK11
      & k1_xboole_0 != sK9
      & k1_xboole_0 != sK8
      & ! [X5,X4] :
          ( ( ( k1_funct_1(sK11,X4) = X5
              & r2_hidden(X4,sK9) )
            | k1_funct_1(sK10,X5) != X4
            | ~ r2_hidden(X5,sK8) )
          & ( ( k1_funct_1(sK10,X5) = X4
              & r2_hidden(X5,sK8) )
            | k1_funct_1(sK11,X4) != X5
            | ~ r2_hidden(X4,sK9) ) )
      & v2_funct_1(sK10)
      & sK9 = k2_relset_1(sK8,sK9,sK10)
      & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK8)))
      & v1_funct_2(sK11,sK9,sK8)
      & v1_funct_1(sK11) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & ! [X4,X5] :
              ( ( ( k1_funct_1(X3,X4) = X5
                  & r2_hidden(X4,X1) )
                | k1_funct_1(X2,X5) != X4
                | ~ r2_hidden(X5,X0) )
              & ( ( k1_funct_1(X2,X5) = X4
                  & r2_hidden(X5,X0) )
                | k1_funct_1(X3,X4) != X5
                | ~ r2_hidden(X4,X1) ) )
          & v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & ! [X4,X5] :
              ( ( ( k1_funct_1(X3,X4) = X5
                  & r2_hidden(X4,X1) )
                | k1_funct_1(X2,X5) != X4
                | ~ r2_hidden(X5,X0) )
              & ( ( k1_funct_1(X2,X5) = X4
                  & r2_hidden(X5,X0) )
                | k1_funct_1(X3,X4) != X5
                | ~ r2_hidden(X4,X1) ) )
          & v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( ! [X4,X5] :
                    ( ( ( k1_funct_1(X2,X5) = X4
                        & r2_hidden(X5,X0) )
                     => ( k1_funct_1(X3,X4) = X5
                        & r2_hidden(X4,X1) ) )
                    & ( ( k1_funct_1(X3,X4) = X5
                        & r2_hidden(X4,X1) )
                     => ( k1_funct_1(X2,X5) = X4
                        & r2_hidden(X5,X0) ) ) )
                & v2_funct_1(X2)
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( ! [X4,X5] :
                  ( ( ( k1_funct_1(X2,X5) = X4
                      & r2_hidden(X5,X0) )
                   => ( k1_funct_1(X3,X4) = X5
                      & r2_hidden(X4,X1) ) )
                  & ( ( k1_funct_1(X3,X4) = X5
                      & r2_hidden(X4,X1) )
                   => ( k1_funct_1(X2,X5) = X4
                      & r2_hidden(X5,X0) ) ) )
              & v2_funct_1(X2)
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_2)).

fof(f820,plain,
    ( r2_hidden(sK15(sK13(sK10,sK11),sK10),sK8)
    | ~ spl16_50 ),
    inference(avatar_component_clause,[],[f818])).

fof(f828,plain,
    ( spl16_50
    | ~ spl16_30
    | ~ spl16_45 ),
    inference(avatar_split_clause,[],[f810,f770,f487,f818])).

fof(f487,plain,
    ( spl16_30
  <=> sK8 = k1_relat_1(sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_30])])).

fof(f770,plain,
    ( spl16_45
  <=> sP2(sK13(sK10,sK11),sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_45])])).

fof(f810,plain,
    ( r2_hidden(sK15(sK13(sK10,sK11),sK10),sK8)
    | ~ spl16_30
    | ~ spl16_45 ),
    inference(unit_resulting_resolution,[],[f772,f525])).

fof(f525,plain,
    ( ! [X0] :
        ( r2_hidden(sK15(X0,sK10),sK8)
        | ~ sP2(X0,sK10) )
    | ~ spl16_30 ),
    inference(superposition,[],[f82,f489])).

fof(f489,plain,
    ( sK8 = k1_relat_1(sK10)
    | ~ spl16_30 ),
    inference(avatar_component_clause,[],[f487])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK15(X0,X1),k1_relat_1(X1))
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ! [X2] :
            ( k1_funct_1(X1,X2) != X0
            | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
      & ( ( k1_funct_1(X1,sK15(X0,X1)) = X0
          & r2_hidden(sK15(X0,X1),k1_relat_1(X1)) )
        | ~ sP2(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f46,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X1,X3) = X0
          & r2_hidden(X3,k1_relat_1(X1)) )
     => ( k1_funct_1(X1,sK15(X0,X1)) = X0
        & r2_hidden(sK15(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ! [X2] :
            ( k1_funct_1(X1,X2) != X0
            | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
      & ( ? [X3] :
            ( k1_funct_1(X1,X3) = X0
            & r2_hidden(X3,k1_relat_1(X1)) )
        | ~ sP2(X0,X1) ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X2,X0] :
      ( ( sP2(X2,X0)
        | ! [X3] :
            ( k1_funct_1(X0,X3) != X2
            | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
      & ( ? [X3] :
            ( k1_funct_1(X0,X3) = X2
            & r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP2(X2,X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X2,X0] :
      ( sP2(X2,X0)
    <=> ? [X3] :
          ( k1_funct_1(X0,X3) = X2
          & r2_hidden(X3,k1_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f772,plain,
    ( sP2(sK13(sK10,sK11),sK10)
    | ~ spl16_45 ),
    inference(avatar_component_clause,[],[f770])).

fof(f826,plain,
    ( spl16_51
    | ~ spl16_45 ),
    inference(avatar_split_clause,[],[f812,f770,f823])).

fof(f812,plain,
    ( sK13(sK10,sK11) = k1_funct_1(sK10,sK15(sK13(sK10,sK11),sK10))
    | ~ spl16_45 ),
    inference(unit_resulting_resolution,[],[f772,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X1,sK15(X0,X1)) = X0
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f773,plain,
    ( spl16_45
    | ~ spl16_24
    | ~ spl16_40 ),
    inference(avatar_split_clause,[],[f768,f734,f387,f770])).

fof(f387,plain,
    ( spl16_24
  <=> sP3(sK10,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_24])])).

fof(f734,plain,
    ( spl16_40
  <=> r2_hidden(sK13(sK10,sK11),sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_40])])).

fof(f768,plain,
    ( sP2(sK13(sK10,sK11),sK10)
    | ~ spl16_24
    | ~ spl16_40 ),
    inference(unit_resulting_resolution,[],[f389,f736,f78])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( ~ sP3(X0,X1)
      | ~ r2_hidden(X3,X1)
      | sP2(X3,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ( ( ~ sP2(sK14(X0,X1),X0)
            | ~ r2_hidden(sK14(X0,X1),X1) )
          & ( sP2(sK14(X0,X1),X0)
            | r2_hidden(sK14(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ sP2(X3,X0) )
            & ( sP2(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP3(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f42,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ sP2(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( sP2(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ sP2(sK14(X0,X1),X0)
          | ~ r2_hidden(sK14(X0,X1),X1) )
        & ( sP2(sK14(X0,X1),X0)
          | r2_hidden(sK14(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ? [X2] :
            ( ( ~ sP2(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( sP2(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ sP2(X3,X0) )
            & ( sP2(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP3(X0,X1) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ? [X2] :
            ( ( ~ sP2(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( sP2(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ sP2(X2,X0) )
            & ( sP2(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP3(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> sP2(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f736,plain,
    ( r2_hidden(sK13(sK10,sK11),sK9)
    | ~ spl16_40 ),
    inference(avatar_component_clause,[],[f734])).

fof(f389,plain,
    ( sP3(sK10,sK9)
    | ~ spl16_24 ),
    inference(avatar_component_clause,[],[f387])).

fof(f763,plain,
    ( spl16_44
    | ~ spl16_39 ),
    inference(avatar_split_clause,[],[f746,f728,f760])).

fof(f728,plain,
    ( spl16_39
  <=> r2_hidden(sK12(sK10,sK11),sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_39])])).

fof(f746,plain,
    ( sK12(sK10,sK11) = k1_funct_1(sK11,k1_funct_1(sK10,sK12(sK10,sK11)))
    | ~ spl16_39 ),
    inference(unit_resulting_resolution,[],[f730,f97])).

fof(f730,plain,
    ( r2_hidden(sK12(sK10,sK11),sK8)
    | ~ spl16_39 ),
    inference(avatar_component_clause,[],[f728])).

fof(f744,plain,
    ( spl16_39
    | ~ spl16_30
    | ~ spl16_38 ),
    inference(avatar_split_clause,[],[f721,f717,f487,f728])).

fof(f721,plain,
    ( r2_hidden(sK12(sK10,sK11),sK8)
    | ~ spl16_30
    | ~ spl16_38 ),
    inference(unit_resulting_resolution,[],[f719,f527])).

fof(f527,plain,
    ( ! [X2] :
        ( r2_hidden(sK12(sK10,X2),sK8)
        | ~ sP1(sK10,X2) )
    | ~ spl16_30 ),
    inference(superposition,[],[f70,f489])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK12(X0,X1),k1_relat_1(X0))
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f743,plain,
    ( spl16_40
    | ~ spl16_31
    | ~ spl16_38 ),
    inference(avatar_split_clause,[],[f722,f717,f495,f734])).

fof(f495,plain,
    ( spl16_31
  <=> sK9 = k1_relat_1(sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_31])])).

fof(f722,plain,
    ( r2_hidden(sK13(sK10,sK11),sK9)
    | ~ spl16_31
    | ~ spl16_38 ),
    inference(unit_resulting_resolution,[],[f719,f529])).

fof(f529,plain,
    ( ! [X1] :
        ( r2_hidden(sK13(X1,sK11),sK9)
        | ~ sP1(X1,sK11) )
    | ~ spl16_31 ),
    inference(superposition,[],[f71,f497])).

fof(f497,plain,
    ( sK9 = k1_relat_1(sK11)
    | ~ spl16_31 ),
    inference(avatar_component_clause,[],[f495])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK13(X0,X1),k1_relat_1(X1))
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f742,plain,
    ( spl16_41
    | ~ spl16_38 ),
    inference(avatar_split_clause,[],[f723,f717,f739])).

fof(f723,plain,
    ( sP0(sK12(sK10,sK11),sK13(sK10,sK11),sK11,sK10)
    | ~ spl16_38 ),
    inference(unit_resulting_resolution,[],[f719,f72])).

fof(f720,plain,
    ( spl16_38
    | spl16_1
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_12
    | ~ spl16_13
    | ~ spl16_22
    | ~ spl16_30
    | ~ spl16_31
    | ~ spl16_35 ),
    inference(avatar_split_clause,[],[f713,f606,f495,f487,f370,f177,f172,f159,f144,f124,f109,f717])).

fof(f109,plain,
    ( spl16_1
  <=> k2_funct_1(sK10) = sK11 ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_1])])).

fof(f124,plain,
    ( spl16_4
  <=> v2_funct_1(sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_4])])).

fof(f144,plain,
    ( spl16_8
  <=> v1_funct_1(sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_8])])).

fof(f159,plain,
    ( spl16_11
  <=> v1_funct_1(sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_11])])).

fof(f172,plain,
    ( spl16_12
  <=> v1_relat_1(sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_12])])).

fof(f177,plain,
    ( spl16_13
  <=> v1_relat_1(sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_13])])).

fof(f370,plain,
    ( spl16_22
  <=> sK9 = k2_relat_1(sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_22])])).

fof(f606,plain,
    ( spl16_35
  <=> sK8 = k2_relat_1(sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_35])])).

fof(f713,plain,
    ( sP1(sK10,sK11)
    | spl16_1
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_12
    | ~ spl16_13
    | ~ spl16_22
    | ~ spl16_30
    | ~ spl16_31
    | ~ spl16_35 ),
    inference(unit_resulting_resolution,[],[f179,f146,f497,f608,f111,f568])).

fof(f568,plain,
    ( ! [X0] :
        ( k2_funct_1(sK10) = X0
        | k2_relat_1(X0) != sK8
        | sP1(sK10,X0)
        | k1_relat_1(X0) != sK9
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl16_4
    | ~ spl16_11
    | ~ spl16_12
    | ~ spl16_22
    | ~ spl16_30 ),
    inference(forward_demodulation,[],[f567,f372])).

fof(f372,plain,
    ( sK9 = k2_relat_1(sK10)
    | ~ spl16_22 ),
    inference(avatar_component_clause,[],[f370])).

fof(f567,plain,
    ( ! [X0] :
        ( k2_relat_1(X0) != sK8
        | sP1(sK10,X0)
        | k1_relat_1(X0) != k2_relat_1(sK10)
        | k2_funct_1(sK10) = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl16_4
    | ~ spl16_11
    | ~ spl16_12
    | ~ spl16_30 ),
    inference(subsumption_resolution,[],[f566,f174])).

fof(f174,plain,
    ( v1_relat_1(sK10)
    | ~ spl16_12 ),
    inference(avatar_component_clause,[],[f172])).

fof(f566,plain,
    ( ! [X0] :
        ( k2_relat_1(X0) != sK8
        | sP1(sK10,X0)
        | k1_relat_1(X0) != k2_relat_1(sK10)
        | k2_funct_1(sK10) = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK10) )
    | ~ spl16_4
    | ~ spl16_11
    | ~ spl16_30 ),
    inference(subsumption_resolution,[],[f565,f161])).

fof(f161,plain,
    ( v1_funct_1(sK10)
    | ~ spl16_11 ),
    inference(avatar_component_clause,[],[f159])).

fof(f565,plain,
    ( ! [X0] :
        ( k2_relat_1(X0) != sK8
        | sP1(sK10,X0)
        | k1_relat_1(X0) != k2_relat_1(sK10)
        | k2_funct_1(sK10) = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(sK10)
        | ~ v1_relat_1(sK10) )
    | ~ spl16_4
    | ~ spl16_30 ),
    inference(subsumption_resolution,[],[f562,f126])).

fof(f126,plain,
    ( v2_funct_1(sK10)
    | ~ spl16_4 ),
    inference(avatar_component_clause,[],[f124])).

fof(f562,plain,
    ( ! [X0] :
        ( k2_relat_1(X0) != sK8
        | sP1(sK10,X0)
        | k1_relat_1(X0) != k2_relat_1(sK10)
        | k2_funct_1(sK10) = X0
        | ~ v2_funct_1(sK10)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(sK10)
        | ~ v1_relat_1(sK10) )
    | ~ spl16_30 ),
    inference(superposition,[],[f75,f489])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != k2_relat_1(X1)
      | sP1(X0,X1)
      | k2_relat_1(X0) != k1_relat_1(X1)
      | k2_funct_1(X0) = X1
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | sP1(X0,X1)
          | k2_relat_1(X0) != k1_relat_1(X1)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f14,f22,f21])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | ? [X2,X3] :
              ( ( k1_funct_1(X0,X2) = X3
              <~> k1_funct_1(X1,X3) = X2 )
              & r2_hidden(X3,k1_relat_1(X1))
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k2_relat_1(X0) != k1_relat_1(X1)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | ? [X2,X3] :
              ( ( k1_funct_1(X0,X2) = X3
              <~> k1_funct_1(X1,X3) = X2 )
              & r2_hidden(X3,k1_relat_1(X1))
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k2_relat_1(X0) != k1_relat_1(X1)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2,X3] :
                  ( ( r2_hidden(X3,k1_relat_1(X1))
                    & r2_hidden(X2,k1_relat_1(X0)) )
                 => ( k1_funct_1(X0,X2) = X3
                  <=> k1_funct_1(X1,X3) = X2 ) )
              & k2_relat_1(X0) = k1_relat_1(X1)
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_1)).

fof(f111,plain,
    ( k2_funct_1(sK10) != sK11
    | spl16_1 ),
    inference(avatar_component_clause,[],[f109])).

fof(f608,plain,
    ( sK8 = k2_relat_1(sK11)
    | ~ spl16_35 ),
    inference(avatar_component_clause,[],[f606])).

fof(f146,plain,
    ( v1_funct_1(sK11)
    | ~ spl16_8 ),
    inference(avatar_component_clause,[],[f144])).

fof(f179,plain,
    ( v1_relat_1(sK11)
    | ~ spl16_13 ),
    inference(avatar_component_clause,[],[f177])).

fof(f609,plain,
    ( spl16_35
    | ~ spl16_15
    | ~ spl16_34 ),
    inference(avatar_split_clause,[],[f601,f591,f193,f606])).

fof(f193,plain,
    ( spl16_15
  <=> sP4(sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_15])])).

fof(f591,plain,
    ( spl16_34
  <=> sP3(sK11,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_34])])).

fof(f601,plain,
    ( sK8 = k2_relat_1(sK11)
    | ~ spl16_15
    | ~ spl16_34 ),
    inference(unit_resulting_resolution,[],[f195,f593,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | ~ sP3(X0,X1)
      | ~ sP4(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ~ sP3(X0,X1) )
          & ( sP3(X0,X1)
            | k2_relat_1(X0) != X1 ) )
      | ~ sP4(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> sP3(X0,X1) )
      | ~ sP4(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f593,plain,
    ( sP3(sK11,sK8)
    | ~ spl16_34 ),
    inference(avatar_component_clause,[],[f591])).

fof(f195,plain,
    ( sP4(sK11)
    | ~ spl16_15 ),
    inference(avatar_component_clause,[],[f193])).

fof(f594,plain,
    ( spl16_34
    | ~ spl16_31 ),
    inference(avatar_split_clause,[],[f589,f495,f591])).

fof(f589,plain,
    ( sP3(sK11,sK8)
    | ~ spl16_31 ),
    inference(subsumption_resolution,[],[f587,f531])).

fof(f531,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK14(sK11,X0),sK8)
        | sP3(sK11,X0)
        | ~ r2_hidden(sK14(sK11,X0),X0) )
    | ~ spl16_31 ),
    inference(resolution,[],[f514,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ sP2(sK14(X0,X1),X0)
      | sP3(X0,X1)
      | ~ r2_hidden(sK14(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f514,plain,
    ( ! [X0] :
        ( sP2(X0,sK11)
        | ~ r2_hidden(X0,sK8) )
    | ~ spl16_31 ),
    inference(subsumption_resolution,[],[f507,f98])).

fof(f98,plain,(
    ! [X5] :
      ( r2_hidden(k1_funct_1(sK10,X5),sK9)
      | ~ r2_hidden(X5,sK8) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X4,X5] :
      ( r2_hidden(X4,sK9)
      | k1_funct_1(sK10,X5) != X4
      | ~ r2_hidden(X5,sK8) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f507,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_funct_1(sK10,X0),sK9)
        | sP2(X0,sK11)
        | ~ r2_hidden(X0,sK8) )
    | ~ spl16_31 ),
    inference(backward_demodulation,[],[f229,f497])).

fof(f229,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_funct_1(sK10,X0),k1_relat_1(sK11))
      | sP2(X0,sK11)
      | ~ r2_hidden(X0,sK8) ) ),
    inference(superposition,[],[f103,f97])).

fof(f103,plain,(
    ! [X2,X1] :
      ( sP2(k1_funct_1(X1,X2),X1)
      | ~ r2_hidden(X2,k1_relat_1(X1)) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1)
      | k1_funct_1(X1,X2) != X0
      | ~ r2_hidden(X2,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f587,plain,
    ( r2_hidden(sK14(sK11,sK8),sK8)
    | sP3(sK11,sK8)
    | ~ spl16_31 ),
    inference(factoring,[],[f560])).

fof(f560,plain,
    ( ! [X2] :
        ( r2_hidden(sK14(sK11,X2),sK8)
        | sP3(sK11,X2)
        | r2_hidden(sK14(sK11,X2),X2) )
    | ~ spl16_31 ),
    inference(resolution,[],[f557,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( sP2(sK14(X0,X1),X0)
      | sP3(X0,X1)
      | r2_hidden(sK14(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f557,plain,
    ( ! [X0] :
        ( ~ sP2(X0,sK11)
        | r2_hidden(X0,sK8) )
    | ~ spl16_31 ),
    inference(duplicate_literal_removal,[],[f552])).

fof(f552,plain,
    ( ! [X0] :
        ( ~ sP2(X0,sK11)
        | r2_hidden(X0,sK8)
        | ~ sP2(X0,sK11) )
    | ~ spl16_31 ),
    inference(resolution,[],[f528,f236])).

fof(f236,plain,(
    ! [X4] :
      ( ~ r2_hidden(sK15(X4,sK11),sK9)
      | r2_hidden(X4,sK8)
      | ~ sP2(X4,sK11) ) ),
    inference(superposition,[],[f100,f83])).

% (13568)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f100,plain,(
    ! [X4] :
      ( r2_hidden(k1_funct_1(sK11,X4),sK8)
      | ~ r2_hidden(X4,sK9) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X5] :
      ( r2_hidden(X5,sK8)
      | k1_funct_1(sK11,X4) != X5
      | ~ r2_hidden(X4,sK9) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f528,plain,
    ( ! [X0] :
        ( r2_hidden(sK15(X0,sK11),sK9)
        | ~ sP2(X0,sK11) )
    | ~ spl16_31 ),
    inference(superposition,[],[f82,f497])).

fof(f506,plain,
    ( spl16_31
    | spl16_3
    | ~ spl16_7
    | ~ spl16_19
    | ~ spl16_27 ),
    inference(avatar_split_clause,[],[f505,f428,f268,f139,f119,f495])).

fof(f119,plain,
    ( spl16_3
  <=> k1_xboole_0 = sK8 ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_3])])).

fof(f139,plain,
    ( spl16_7
  <=> v1_funct_2(sK11,sK9,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_7])])).

fof(f268,plain,
    ( spl16_19
  <=> sP6(sK9,sK11,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_19])])).

fof(f428,plain,
    ( spl16_27
  <=> k1_relat_1(sK11) = k1_relset_1(sK9,sK8,sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_27])])).

fof(f505,plain,
    ( sK9 = k1_relat_1(sK11)
    | spl16_3
    | ~ spl16_7
    | ~ spl16_19
    | ~ spl16_27 ),
    inference(subsumption_resolution,[],[f504,f270])).

fof(f270,plain,
    ( sP6(sK9,sK11,sK8)
    | ~ spl16_19 ),
    inference(avatar_component_clause,[],[f268])).

fof(f504,plain,
    ( sK9 = k1_relat_1(sK11)
    | ~ sP6(sK9,sK11,sK8)
    | spl16_3
    | ~ spl16_7
    | ~ spl16_27 ),
    inference(subsumption_resolution,[],[f503,f166])).

fof(f166,plain,
    ( ! [X0] : ~ sP5(X0,sK8)
    | spl16_3 ),
    inference(unit_resulting_resolution,[],[f121,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ sP5(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP5(X0,X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP5(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f121,plain,
    ( k1_xboole_0 != sK8
    | spl16_3 ),
    inference(avatar_component_clause,[],[f119])).

fof(f503,plain,
    ( sK9 = k1_relat_1(sK11)
    | sP5(sK9,sK8)
    | ~ sP6(sK9,sK11,sK8)
    | ~ spl16_7
    | ~ spl16_27 ),
    inference(subsumption_resolution,[],[f471,f141])).

fof(f141,plain,
    ( v1_funct_2(sK11,sK9,sK8)
    | ~ spl16_7 ),
    inference(avatar_component_clause,[],[f139])).

fof(f471,plain,
    ( sK9 = k1_relat_1(sK11)
    | ~ v1_funct_2(sK11,sK9,sK8)
    | sP5(sK9,sK8)
    | ~ sP6(sK9,sK11,sK8)
    | ~ spl16_27 ),
    inference(superposition,[],[f430,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP5(X0,X2)
      | ~ sP6(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP5(X0,X2)
      | ~ sP6(X0,X1,X2) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP5(X0,X1)
      | ~ sP6(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP5(X0,X1)
      | ~ sP6(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).

fof(f430,plain,
    ( k1_relat_1(sK11) = k1_relset_1(sK9,sK8,sK11)
    | ~ spl16_27 ),
    inference(avatar_component_clause,[],[f428])).

fof(f502,plain,
    ( spl16_30
    | spl16_2
    | ~ spl16_10
    | ~ spl16_18
    | ~ spl16_26 ),
    inference(avatar_split_clause,[],[f501,f423,f263,f154,f114,f487])).

fof(f114,plain,
    ( spl16_2
  <=> k1_xboole_0 = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_2])])).

fof(f154,plain,
    ( spl16_10
  <=> v1_funct_2(sK10,sK8,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_10])])).

fof(f263,plain,
    ( spl16_18
  <=> sP6(sK8,sK10,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_18])])).

fof(f423,plain,
    ( spl16_26
  <=> k1_relat_1(sK10) = k1_relset_1(sK8,sK9,sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_26])])).

fof(f501,plain,
    ( sK8 = k1_relat_1(sK10)
    | spl16_2
    | ~ spl16_10
    | ~ spl16_18
    | ~ spl16_26 ),
    inference(subsumption_resolution,[],[f500,f265])).

fof(f265,plain,
    ( sP6(sK8,sK10,sK9)
    | ~ spl16_18 ),
    inference(avatar_component_clause,[],[f263])).

fof(f500,plain,
    ( sK8 = k1_relat_1(sK10)
    | ~ sP6(sK8,sK10,sK9)
    | spl16_2
    | ~ spl16_10
    | ~ spl16_26 ),
    inference(subsumption_resolution,[],[f499,f165])).

fof(f165,plain,
    ( ! [X0] : ~ sP5(X0,sK9)
    | spl16_2 ),
    inference(unit_resulting_resolution,[],[f116,f93])).

fof(f116,plain,
    ( k1_xboole_0 != sK9
    | spl16_2 ),
    inference(avatar_component_clause,[],[f114])).

fof(f499,plain,
    ( sK8 = k1_relat_1(sK10)
    | sP5(sK8,sK9)
    | ~ sP6(sK8,sK10,sK9)
    | ~ spl16_10
    | ~ spl16_26 ),
    inference(subsumption_resolution,[],[f470,f156])).

fof(f156,plain,
    ( v1_funct_2(sK10,sK8,sK9)
    | ~ spl16_10 ),
    inference(avatar_component_clause,[],[f154])).

fof(f470,plain,
    ( sK8 = k1_relat_1(sK10)
    | ~ v1_funct_2(sK10,sK8,sK9)
    | sP5(sK8,sK9)
    | ~ sP6(sK8,sK10,sK9)
    | ~ spl16_26 ),
    inference(superposition,[],[f425,f91])).

fof(f425,plain,
    ( k1_relat_1(sK10) = k1_relset_1(sK8,sK9,sK10)
    | ~ spl16_26 ),
    inference(avatar_component_clause,[],[f423])).

fof(f431,plain,
    ( spl16_27
    | ~ spl16_6 ),
    inference(avatar_split_clause,[],[f420,f134,f428])).

fof(f134,plain,
    ( spl16_6
  <=> m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_6])])).

fof(f420,plain,
    ( k1_relat_1(sK11) = k1_relset_1(sK9,sK8,sK11)
    | ~ spl16_6 ),
    inference(unit_resulting_resolution,[],[f136,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f136,plain,
    ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK8)))
    | ~ spl16_6 ),
    inference(avatar_component_clause,[],[f134])).

fof(f426,plain,
    ( spl16_26
    | ~ spl16_9 ),
    inference(avatar_split_clause,[],[f421,f149,f423])).

fof(f149,plain,
    ( spl16_9
  <=> m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_9])])).

fof(f421,plain,
    ( k1_relat_1(sK10) = k1_relset_1(sK8,sK9,sK10)
    | ~ spl16_9 ),
    inference(unit_resulting_resolution,[],[f151,f88])).

fof(f151,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
    | ~ spl16_9 ),
    inference(avatar_component_clause,[],[f149])).

fof(f390,plain,
    ( spl16_24
    | ~ spl16_16
    | ~ spl16_22 ),
    inference(avatar_split_clause,[],[f385,f370,f199,f387])).

fof(f199,plain,
    ( spl16_16
  <=> sP3(sK10,k2_relat_1(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_16])])).

fof(f385,plain,
    ( sP3(sK10,sK9)
    | ~ spl16_16
    | ~ spl16_22 ),
    inference(backward_demodulation,[],[f201,f372])).

fof(f201,plain,
    ( sP3(sK10,k2_relat_1(sK10))
    | ~ spl16_16 ),
    inference(avatar_component_clause,[],[f199])).

% (13567)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f382,plain,
    ( spl16_22
    | ~ spl16_5
    | ~ spl16_9 ),
    inference(avatar_split_clause,[],[f381,f149,f129,f370])).

fof(f129,plain,
    ( spl16_5
  <=> sK9 = k2_relset_1(sK8,sK9,sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_5])])).

fof(f381,plain,
    ( sK9 = k2_relat_1(sK10)
    | ~ spl16_5
    | ~ spl16_9 ),
    inference(subsumption_resolution,[],[f367,f151])).

fof(f367,plain,
    ( sK9 = k2_relat_1(sK10)
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
    | ~ spl16_5 ),
    inference(superposition,[],[f131,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f131,plain,
    ( sK9 = k2_relset_1(sK8,sK9,sK10)
    | ~ spl16_5 ),
    inference(avatar_component_clause,[],[f129])).

fof(f273,plain,
    ( spl16_18
    | ~ spl16_9 ),
    inference(avatar_split_clause,[],[f261,f149,f263])).

fof(f261,plain,
    ( sP6(sK8,sK10,sK9)
    | ~ spl16_9 ),
    inference(resolution,[],[f95,f151])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP6(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( sP7(X2,X1,X0)
        & sP6(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f20,f30,f29,f28])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP7(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).

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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f272,plain,
    ( spl16_19
    | ~ spl16_6 ),
    inference(avatar_split_clause,[],[f260,f134,f268])).

fof(f260,plain,
    ( sP6(sK9,sK11,sK8)
    | ~ spl16_6 ),
    inference(resolution,[],[f95,f136])).

fof(f202,plain,
    ( spl16_16
    | ~ spl16_14 ),
    inference(avatar_split_clause,[],[f197,f187,f199])).

fof(f187,plain,
    ( spl16_14
  <=> sP4(sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_14])])).

fof(f197,plain,
    ( sP3(sK10,k2_relat_1(sK10))
    | ~ spl16_14 ),
    inference(unit_resulting_resolution,[],[f189,f102])).

fof(f102,plain,(
    ! [X0] :
      ( sP3(X0,k2_relat_1(X0))
      | ~ sP4(X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
      | k2_relat_1(X0) != X1
      | ~ sP4(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f189,plain,
    ( sP4(sK10)
    | ~ spl16_14 ),
    inference(avatar_component_clause,[],[f187])).

fof(f196,plain,
    ( spl16_15
    | ~ spl16_8
    | ~ spl16_13 ),
    inference(avatar_split_clause,[],[f191,f177,f144,f193])).

fof(f191,plain,
    ( sP4(sK11)
    | ~ spl16_8
    | ~ spl16_13 ),
    inference(unit_resulting_resolution,[],[f146,f179,f85])).

fof(f85,plain,(
    ! [X0] :
      ( sP4(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( sP4(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f16,f26,f25,f24])).

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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f190,plain,
    ( spl16_14
    | ~ spl16_11
    | ~ spl16_12 ),
    inference(avatar_split_clause,[],[f185,f172,f159,f187])).

fof(f185,plain,
    ( sP4(sK10)
    | ~ spl16_11
    | ~ spl16_12 ),
    inference(unit_resulting_resolution,[],[f161,f174,f85])).

fof(f184,plain,
    ( spl16_12
    | ~ spl16_9 ),
    inference(avatar_split_clause,[],[f183,f149,f172])).

fof(f183,plain,
    ( v1_relat_1(sK10)
    | ~ spl16_9 ),
    inference(subsumption_resolution,[],[f170,f86])).

fof(f86,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f170,plain,
    ( v1_relat_1(sK10)
    | ~ v1_relat_1(k2_zfmisc_1(sK8,sK9))
    | ~ spl16_9 ),
    inference(resolution,[],[f69,f151])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f182,plain,
    ( spl16_13
    | ~ spl16_6 ),
    inference(avatar_split_clause,[],[f181,f134,f177])).

fof(f181,plain,
    ( v1_relat_1(sK11)
    | ~ spl16_6 ),
    inference(subsumption_resolution,[],[f169,f86])).

fof(f169,plain,
    ( v1_relat_1(sK11)
    | ~ v1_relat_1(k2_zfmisc_1(sK9,sK8))
    | ~ spl16_6 ),
    inference(resolution,[],[f69,f136])).

fof(f162,plain,(
    spl16_11 ),
    inference(avatar_split_clause,[],[f54,f159])).

fof(f54,plain,(
    v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f34])).

fof(f157,plain,(
    spl16_10 ),
    inference(avatar_split_clause,[],[f55,f154])).

fof(f55,plain,(
    v1_funct_2(sK10,sK8,sK9) ),
    inference(cnf_transformation,[],[f34])).

fof(f152,plain,(
    spl16_9 ),
    inference(avatar_split_clause,[],[f56,f149])).

fof(f56,plain,(
    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) ),
    inference(cnf_transformation,[],[f34])).

fof(f147,plain,(
    spl16_8 ),
    inference(avatar_split_clause,[],[f57,f144])).

fof(f57,plain,(
    v1_funct_1(sK11) ),
    inference(cnf_transformation,[],[f34])).

fof(f142,plain,(
    spl16_7 ),
    inference(avatar_split_clause,[],[f58,f139])).

fof(f58,plain,(
    v1_funct_2(sK11,sK9,sK8) ),
    inference(cnf_transformation,[],[f34])).

fof(f137,plain,(
    spl16_6 ),
    inference(avatar_split_clause,[],[f59,f134])).

fof(f59,plain,(
    m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK8))) ),
    inference(cnf_transformation,[],[f34])).

fof(f132,plain,(
    spl16_5 ),
    inference(avatar_split_clause,[],[f60,f129])).

fof(f60,plain,(
    sK9 = k2_relset_1(sK8,sK9,sK10) ),
    inference(cnf_transformation,[],[f34])).

fof(f127,plain,(
    spl16_4 ),
    inference(avatar_split_clause,[],[f61,f124])).

fof(f61,plain,(
    v2_funct_1(sK10) ),
    inference(cnf_transformation,[],[f34])).

fof(f122,plain,(
    ~ spl16_3 ),
    inference(avatar_split_clause,[],[f66,f119])).

fof(f66,plain,(
    k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f34])).

fof(f117,plain,(
    ~ spl16_2 ),
    inference(avatar_split_clause,[],[f67,f114])).

fof(f67,plain,(
    k1_xboole_0 != sK9 ),
    inference(cnf_transformation,[],[f34])).

fof(f112,plain,(
    ~ spl16_1 ),
    inference(avatar_split_clause,[],[f68,f109])).

fof(f68,plain,(
    k2_funct_1(sK10) != sK11 ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:30:49 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (13559)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.47  % (13562)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (13566)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.48  % (13565)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.48  % (13557)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.49  % (13555)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (13564)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (13550)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (13554)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (13569)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.50  % (13553)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (13556)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  % (13552)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  % (13551)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (13563)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.52  % (13566)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (13561)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.52  % (13561)Refutation not found, incomplete strategy% (13561)------------------------------
% 0.22/0.52  % (13561)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (13561)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (13561)Memory used [KB]: 10746
% 0.22/0.52  % (13561)Time elapsed: 0.109 s
% 0.22/0.52  % (13561)------------------------------
% 0.22/0.52  % (13561)------------------------------
% 0.22/0.52  % (13560)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f1313,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f112,f117,f122,f127,f132,f137,f142,f147,f152,f157,f162,f182,f184,f190,f196,f202,f272,f273,f382,f390,f426,f431,f502,f506,f594,f609,f720,f742,f743,f744,f763,f773,f826,f828,f901,f960,f961,f975,f1312])).
% 0.22/0.52  fof(f1312,plain,(
% 0.22/0.52    ~spl16_38 | ~spl16_62 | ~spl16_63),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f1311])).
% 0.22/0.52  fof(f1311,plain,(
% 0.22/0.52    $false | (~spl16_38 | ~spl16_62 | ~spl16_63)),
% 0.22/0.52    inference(subsumption_resolution,[],[f1310,f719])).
% 0.22/0.52  fof(f719,plain,(
% 0.22/0.52    sP1(sK10,sK11) | ~spl16_38),
% 0.22/0.52    inference(avatar_component_clause,[],[f717])).
% 0.22/0.52  fof(f717,plain,(
% 0.22/0.52    spl16_38 <=> sP1(sK10,sK11)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl16_38])])).
% 0.22/0.52  fof(f1310,plain,(
% 0.22/0.52    ~sP1(sK10,sK11) | (~spl16_62 | ~spl16_63)),
% 0.22/0.52    inference(subsumption_resolution,[],[f1302,f959])).
% 0.22/0.52  fof(f959,plain,(
% 0.22/0.52    sK13(sK10,sK11) = k1_funct_1(sK10,sK12(sK10,sK11)) | ~spl16_63),
% 0.22/0.52    inference(avatar_component_clause,[],[f957])).
% 0.22/0.52  fof(f957,plain,(
% 0.22/0.52    spl16_63 <=> sK13(sK10,sK11) = k1_funct_1(sK10,sK12(sK10,sK11))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl16_63])])).
% 0.22/0.52  fof(f1302,plain,(
% 0.22/0.52    sK13(sK10,sK11) != k1_funct_1(sK10,sK12(sK10,sK11)) | ~sP1(sK10,sK11) | ~spl16_62),
% 0.22/0.52    inference(resolution,[],[f998,f72])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    ( ! [X0,X1] : (sP0(sK12(X0,X1),sK13(X0,X1),X1,X0) | ~sP1(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ! [X0,X1] : ((sP0(sK12(X0,X1),sK13(X0,X1),X1,X0) & r2_hidden(sK13(X0,X1),k1_relat_1(X1)) & r2_hidden(sK12(X0,X1),k1_relat_1(X0))) | ~sP1(X0,X1))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13])],[f35,f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ! [X1,X0] : (? [X2,X3] : (sP0(X2,X3,X1,X0) & r2_hidden(X3,k1_relat_1(X1)) & r2_hidden(X2,k1_relat_1(X0))) => (sP0(sK12(X0,X1),sK13(X0,X1),X1,X0) & r2_hidden(sK13(X0,X1),k1_relat_1(X1)) & r2_hidden(sK12(X0,X1),k1_relat_1(X0))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ! [X0,X1] : (? [X2,X3] : (sP0(X2,X3,X1,X0) & r2_hidden(X3,k1_relat_1(X1)) & r2_hidden(X2,k1_relat_1(X0))) | ~sP1(X0,X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0,X1] : (? [X2,X3] : (sP0(X2,X3,X1,X0) & r2_hidden(X3,k1_relat_1(X1)) & r2_hidden(X2,k1_relat_1(X0))) | ~sP1(X0,X1))),
% 0.22/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.52  fof(f998,plain,(
% 0.22/0.52    ( ! [X2] : (~sP0(sK12(sK10,sK11),sK13(sK10,sK11),sK11,X2) | sK13(sK10,sK11) != k1_funct_1(X2,sK12(sK10,sK11))) ) | ~spl16_62),
% 0.22/0.52    inference(superposition,[],[f101,f955])).
% 0.22/0.52  fof(f955,plain,(
% 0.22/0.52    sK12(sK10,sK11) = k1_funct_1(sK11,sK13(sK10,sK11)) | ~spl16_62),
% 0.22/0.52    inference(avatar_component_clause,[],[f953])).
% 0.22/0.52  fof(f953,plain,(
% 0.22/0.52    spl16_62 <=> sK12(sK10,sK11) = k1_funct_1(sK11,sK13(sK10,sK11))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl16_62])])).
% 0.22/0.52  fof(f101,plain,(
% 0.22/0.52    ( ! [X2,X3,X1] : (~sP0(k1_funct_1(X2,X1),X1,X2,X3) | k1_funct_1(X3,k1_funct_1(X2,X1)) != X1) )),
% 0.22/0.52    inference(equality_resolution,[],[f74])).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,X1) != X0 | k1_funct_1(X3,X0) != X1 | ~sP0(X0,X1,X2,X3)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (((k1_funct_1(X2,X1) != X0 | k1_funct_1(X3,X0) != X1) & (k1_funct_1(X2,X1) = X0 | k1_funct_1(X3,X0) = X1)) | ~sP0(X0,X1,X2,X3))),
% 0.22/0.52    inference(rectify,[],[f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ! [X2,X3,X1,X0] : (((k1_funct_1(X1,X3) != X2 | k1_funct_1(X0,X2) != X3) & (k1_funct_1(X1,X3) = X2 | k1_funct_1(X0,X2) = X3)) | ~sP0(X2,X3,X1,X0))),
% 0.22/0.52    inference(nnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X2,X3,X1,X0] : ((k1_funct_1(X0,X2) = X3 <~> k1_funct_1(X1,X3) = X2) | ~sP0(X2,X3,X1,X0))),
% 0.22/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.52  fof(f975,plain,(
% 0.22/0.52    spl16_62 | ~spl16_44 | ~spl16_63),
% 0.22/0.52    inference(avatar_split_clause,[],[f967,f957,f760,f953])).
% 0.22/0.52  fof(f760,plain,(
% 0.22/0.52    spl16_44 <=> sK12(sK10,sK11) = k1_funct_1(sK11,k1_funct_1(sK10,sK12(sK10,sK11)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl16_44])])).
% 0.22/0.52  fof(f967,plain,(
% 0.22/0.52    sK12(sK10,sK11) = k1_funct_1(sK11,sK13(sK10,sK11)) | (~spl16_44 | ~spl16_63)),
% 0.22/0.52    inference(backward_demodulation,[],[f762,f959])).
% 0.22/0.52  fof(f762,plain,(
% 0.22/0.52    sK12(sK10,sK11) = k1_funct_1(sK11,k1_funct_1(sK10,sK12(sK10,sK11))) | ~spl16_44),
% 0.22/0.52    inference(avatar_component_clause,[],[f760])).
% 0.22/0.52  fof(f961,plain,(
% 0.22/0.52    sK12(sK10,sK11) != k1_funct_1(sK11,sK13(sK10,sK11)) | k1_funct_1(sK11,sK13(sK10,sK11)) != sK15(sK13(sK10,sK11),sK10) | sK13(sK10,sK11) != k1_funct_1(sK10,sK15(sK13(sK10,sK11),sK10)) | sK13(sK10,sK11) = k1_funct_1(sK10,sK12(sK10,sK11))),
% 0.22/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.52  fof(f960,plain,(
% 0.22/0.52    spl16_62 | spl16_63 | ~spl16_41),
% 0.22/0.52    inference(avatar_split_clause,[],[f951,f739,f957,f953])).
% 0.22/0.52  fof(f739,plain,(
% 0.22/0.52    spl16_41 <=> sP0(sK12(sK10,sK11),sK13(sK10,sK11),sK11,sK10)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl16_41])])).
% 0.22/0.52  fof(f951,plain,(
% 0.22/0.52    sK13(sK10,sK11) = k1_funct_1(sK10,sK12(sK10,sK11)) | sK12(sK10,sK11) = k1_funct_1(sK11,sK13(sK10,sK11)) | ~spl16_41),
% 0.22/0.52    inference(resolution,[],[f741,f73])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3) | k1_funct_1(X3,X0) = X1 | k1_funct_1(X2,X1) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f39])).
% 0.22/0.52  fof(f741,plain,(
% 0.22/0.52    sP0(sK12(sK10,sK11),sK13(sK10,sK11),sK11,sK10) | ~spl16_41),
% 0.22/0.52    inference(avatar_component_clause,[],[f739])).
% 0.22/0.52  fof(f901,plain,(
% 0.22/0.52    spl16_57 | ~spl16_50 | ~spl16_51),
% 0.22/0.52    inference(avatar_split_clause,[],[f896,f823,f818,f898])).
% 0.22/0.52  fof(f898,plain,(
% 0.22/0.52    spl16_57 <=> k1_funct_1(sK11,sK13(sK10,sK11)) = sK15(sK13(sK10,sK11),sK10)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl16_57])])).
% 0.22/0.52  fof(f818,plain,(
% 0.22/0.52    spl16_50 <=> r2_hidden(sK15(sK13(sK10,sK11),sK10),sK8)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl16_50])])).
% 0.22/0.52  fof(f823,plain,(
% 0.22/0.52    spl16_51 <=> sK13(sK10,sK11) = k1_funct_1(sK10,sK15(sK13(sK10,sK11),sK10))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl16_51])])).
% 0.22/0.52  fof(f896,plain,(
% 0.22/0.52    k1_funct_1(sK11,sK13(sK10,sK11)) = sK15(sK13(sK10,sK11),sK10) | (~spl16_50 | ~spl16_51)),
% 0.22/0.52    inference(forward_demodulation,[],[f884,f825])).
% 0.22/0.52  fof(f825,plain,(
% 0.22/0.52    sK13(sK10,sK11) = k1_funct_1(sK10,sK15(sK13(sK10,sK11),sK10)) | ~spl16_51),
% 0.22/0.52    inference(avatar_component_clause,[],[f823])).
% 0.22/0.52  fof(f884,plain,(
% 0.22/0.52    sK15(sK13(sK10,sK11),sK10) = k1_funct_1(sK11,k1_funct_1(sK10,sK15(sK13(sK10,sK11),sK10))) | ~spl16_50),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f820,f97])).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    ( ! [X5] : (k1_funct_1(sK11,k1_funct_1(sK10,X5)) = X5 | ~r2_hidden(X5,sK8)) )),
% 0.22/0.52    inference(equality_resolution,[],[f65])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    ( ! [X4,X5] : (k1_funct_1(sK11,X4) = X5 | k1_funct_1(sK10,X5) != X4 | ~r2_hidden(X5,sK8)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    (k2_funct_1(sK10) != sK11 & k1_xboole_0 != sK9 & k1_xboole_0 != sK8 & ! [X4,X5] : (((k1_funct_1(sK11,X4) = X5 & r2_hidden(X4,sK9)) | k1_funct_1(sK10,X5) != X4 | ~r2_hidden(X5,sK8)) & ((k1_funct_1(sK10,X5) = X4 & r2_hidden(X5,sK8)) | k1_funct_1(sK11,X4) != X5 | ~r2_hidden(X4,sK9))) & v2_funct_1(sK10) & sK9 = k2_relset_1(sK8,sK9,sK10) & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK8))) & v1_funct_2(sK11,sK9,sK8) & v1_funct_1(sK11)) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) & v1_funct_2(sK10,sK8,sK9) & v1_funct_1(sK10)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f11,f33,f32])).
% 0.22/0.52  % (13558)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X4,X5] : (((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1)) | k1_funct_1(X2,X5) != X4 | ~r2_hidden(X5,X0)) & ((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) | k1_funct_1(X3,X4) != X5 | ~r2_hidden(X4,X1))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK10) != X3 & k1_xboole_0 != sK9 & k1_xboole_0 != sK8 & ! [X5,X4] : (((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,sK9)) | k1_funct_1(sK10,X5) != X4 | ~r2_hidden(X5,sK8)) & ((k1_funct_1(sK10,X5) = X4 & r2_hidden(X5,sK8)) | k1_funct_1(X3,X4) != X5 | ~r2_hidden(X4,sK9))) & v2_funct_1(sK10) & sK9 = k2_relset_1(sK8,sK9,sK10) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK9,sK8))) & v1_funct_2(X3,sK9,sK8) & v1_funct_1(X3)) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) & v1_funct_2(sK10,sK8,sK9) & v1_funct_1(sK10))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ? [X3] : (k2_funct_1(sK10) != X3 & k1_xboole_0 != sK9 & k1_xboole_0 != sK8 & ! [X5,X4] : (((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,sK9)) | k1_funct_1(sK10,X5) != X4 | ~r2_hidden(X5,sK8)) & ((k1_funct_1(sK10,X5) = X4 & r2_hidden(X5,sK8)) | k1_funct_1(X3,X4) != X5 | ~r2_hidden(X4,sK9))) & v2_funct_1(sK10) & sK9 = k2_relset_1(sK8,sK9,sK10) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK9,sK8))) & v1_funct_2(X3,sK9,sK8) & v1_funct_1(X3)) => (k2_funct_1(sK10) != sK11 & k1_xboole_0 != sK9 & k1_xboole_0 != sK8 & ! [X5,X4] : (((k1_funct_1(sK11,X4) = X5 & r2_hidden(X4,sK9)) | k1_funct_1(sK10,X5) != X4 | ~r2_hidden(X5,sK8)) & ((k1_funct_1(sK10,X5) = X4 & r2_hidden(X5,sK8)) | k1_funct_1(sK11,X4) != X5 | ~r2_hidden(X4,sK9))) & v2_funct_1(sK10) & sK9 = k2_relset_1(sK8,sK9,sK10) & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK8))) & v1_funct_2(sK11,sK9,sK8) & v1_funct_1(sK11))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X4,X5] : (((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1)) | k1_funct_1(X2,X5) != X4 | ~r2_hidden(X5,X0)) & ((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) | k1_funct_1(X3,X4) != X5 | ~r2_hidden(X4,X1))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.52    inference(flattening,[],[f10])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (! [X4,X5] : (((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1)) | (k1_funct_1(X2,X5) != X4 | ~r2_hidden(X5,X0))) & ((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) | (k1_funct_1(X3,X4) != X5 | ~r2_hidden(X4,X1)))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((! [X4,X5] : (((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) => (k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1))) & ((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1)) => (k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.22/0.52    inference(negated_conjecture,[],[f8])).
% 0.22/0.52  fof(f8,conjecture,(
% 0.22/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((! [X4,X5] : (((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) => (k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1))) & ((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1)) => (k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_2)).
% 0.22/0.52  fof(f820,plain,(
% 0.22/0.52    r2_hidden(sK15(sK13(sK10,sK11),sK10),sK8) | ~spl16_50),
% 0.22/0.52    inference(avatar_component_clause,[],[f818])).
% 0.22/0.52  fof(f828,plain,(
% 0.22/0.52    spl16_50 | ~spl16_30 | ~spl16_45),
% 0.22/0.52    inference(avatar_split_clause,[],[f810,f770,f487,f818])).
% 0.22/0.52  fof(f487,plain,(
% 0.22/0.52    spl16_30 <=> sK8 = k1_relat_1(sK10)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl16_30])])).
% 0.22/0.52  fof(f770,plain,(
% 0.22/0.52    spl16_45 <=> sP2(sK13(sK10,sK11),sK10)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl16_45])])).
% 0.22/0.52  fof(f810,plain,(
% 0.22/0.52    r2_hidden(sK15(sK13(sK10,sK11),sK10),sK8) | (~spl16_30 | ~spl16_45)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f772,f525])).
% 0.22/0.52  fof(f525,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(sK15(X0,sK10),sK8) | ~sP2(X0,sK10)) ) | ~spl16_30),
% 0.22/0.52    inference(superposition,[],[f82,f489])).
% 0.22/0.52  fof(f489,plain,(
% 0.22/0.52    sK8 = k1_relat_1(sK10) | ~spl16_30),
% 0.22/0.52    inference(avatar_component_clause,[],[f487])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(sK15(X0,X1),k1_relat_1(X1)) | ~sP2(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f48])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ! [X0,X1] : ((sP2(X0,X1) | ! [X2] : (k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1)))) & ((k1_funct_1(X1,sK15(X0,X1)) = X0 & r2_hidden(sK15(X0,X1),k1_relat_1(X1))) | ~sP2(X0,X1)))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f46,f47])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ! [X1,X0] : (? [X3] : (k1_funct_1(X1,X3) = X0 & r2_hidden(X3,k1_relat_1(X1))) => (k1_funct_1(X1,sK15(X0,X1)) = X0 & r2_hidden(sK15(X0,X1),k1_relat_1(X1))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    ! [X0,X1] : ((sP2(X0,X1) | ! [X2] : (k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1)))) & (? [X3] : (k1_funct_1(X1,X3) = X0 & r2_hidden(X3,k1_relat_1(X1))) | ~sP2(X0,X1)))),
% 0.22/0.52    inference(rectify,[],[f45])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    ! [X2,X0] : ((sP2(X2,X0) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP2(X2,X0)))),
% 0.22/0.52    inference(nnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X2,X0] : (sP2(X2,X0) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))),
% 0.22/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.52  fof(f772,plain,(
% 0.22/0.52    sP2(sK13(sK10,sK11),sK10) | ~spl16_45),
% 0.22/0.52    inference(avatar_component_clause,[],[f770])).
% 0.22/0.52  fof(f826,plain,(
% 0.22/0.52    spl16_51 | ~spl16_45),
% 0.22/0.52    inference(avatar_split_clause,[],[f812,f770,f823])).
% 0.22/0.52  fof(f812,plain,(
% 0.22/0.52    sK13(sK10,sK11) = k1_funct_1(sK10,sK15(sK13(sK10,sK11),sK10)) | ~spl16_45),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f772,f83])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_funct_1(X1,sK15(X0,X1)) = X0 | ~sP2(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f48])).
% 0.22/0.52  fof(f773,plain,(
% 0.22/0.52    spl16_45 | ~spl16_24 | ~spl16_40),
% 0.22/0.52    inference(avatar_split_clause,[],[f768,f734,f387,f770])).
% 0.22/0.52  fof(f387,plain,(
% 0.22/0.52    spl16_24 <=> sP3(sK10,sK9)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl16_24])])).
% 0.22/0.52  fof(f734,plain,(
% 0.22/0.52    spl16_40 <=> r2_hidden(sK13(sK10,sK11),sK9)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl16_40])])).
% 0.22/0.52  fof(f768,plain,(
% 0.22/0.52    sP2(sK13(sK10,sK11),sK10) | (~spl16_24 | ~spl16_40)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f389,f736,f78])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    ( ! [X0,X3,X1] : (~sP3(X0,X1) | ~r2_hidden(X3,X1) | sP2(X3,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ! [X0,X1] : ((sP3(X0,X1) | ((~sP2(sK14(X0,X1),X0) | ~r2_hidden(sK14(X0,X1),X1)) & (sP2(sK14(X0,X1),X0) | r2_hidden(sK14(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP2(X3,X0)) & (sP2(X3,X0) | ~r2_hidden(X3,X1))) | ~sP3(X0,X1)))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f42,f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ! [X1,X0] : (? [X2] : ((~sP2(X2,X0) | ~r2_hidden(X2,X1)) & (sP2(X2,X0) | r2_hidden(X2,X1))) => ((~sP2(sK14(X0,X1),X0) | ~r2_hidden(sK14(X0,X1),X1)) & (sP2(sK14(X0,X1),X0) | r2_hidden(sK14(X0,X1),X1))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ! [X0,X1] : ((sP3(X0,X1) | ? [X2] : ((~sP2(X2,X0) | ~r2_hidden(X2,X1)) & (sP2(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP2(X3,X0)) & (sP2(X3,X0) | ~r2_hidden(X3,X1))) | ~sP3(X0,X1)))),
% 0.22/0.52    inference(rectify,[],[f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ! [X0,X1] : ((sP3(X0,X1) | ? [X2] : ((~sP2(X2,X0) | ~r2_hidden(X2,X1)) & (sP2(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~sP2(X2,X0)) & (sP2(X2,X0) | ~r2_hidden(X2,X1))) | ~sP3(X0,X1)))),
% 0.22/0.52    inference(nnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0,X1] : (sP3(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> sP2(X2,X0)))),
% 0.22/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.22/0.52  fof(f736,plain,(
% 0.22/0.52    r2_hidden(sK13(sK10,sK11),sK9) | ~spl16_40),
% 0.22/0.52    inference(avatar_component_clause,[],[f734])).
% 0.22/0.52  fof(f389,plain,(
% 0.22/0.52    sP3(sK10,sK9) | ~spl16_24),
% 0.22/0.52    inference(avatar_component_clause,[],[f387])).
% 0.22/0.52  fof(f763,plain,(
% 0.22/0.52    spl16_44 | ~spl16_39),
% 0.22/0.52    inference(avatar_split_clause,[],[f746,f728,f760])).
% 0.22/0.52  fof(f728,plain,(
% 0.22/0.52    spl16_39 <=> r2_hidden(sK12(sK10,sK11),sK8)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl16_39])])).
% 0.22/0.52  fof(f746,plain,(
% 0.22/0.52    sK12(sK10,sK11) = k1_funct_1(sK11,k1_funct_1(sK10,sK12(sK10,sK11))) | ~spl16_39),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f730,f97])).
% 0.22/0.52  fof(f730,plain,(
% 0.22/0.52    r2_hidden(sK12(sK10,sK11),sK8) | ~spl16_39),
% 0.22/0.52    inference(avatar_component_clause,[],[f728])).
% 0.22/0.52  fof(f744,plain,(
% 0.22/0.52    spl16_39 | ~spl16_30 | ~spl16_38),
% 0.22/0.52    inference(avatar_split_clause,[],[f721,f717,f487,f728])).
% 0.22/0.52  fof(f721,plain,(
% 0.22/0.52    r2_hidden(sK12(sK10,sK11),sK8) | (~spl16_30 | ~spl16_38)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f719,f527])).
% 0.22/0.52  fof(f527,plain,(
% 0.22/0.52    ( ! [X2] : (r2_hidden(sK12(sK10,X2),sK8) | ~sP1(sK10,X2)) ) | ~spl16_30),
% 0.22/0.52    inference(superposition,[],[f70,f489])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(sK12(X0,X1),k1_relat_1(X0)) | ~sP1(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f37])).
% 0.22/0.52  fof(f743,plain,(
% 0.22/0.52    spl16_40 | ~spl16_31 | ~spl16_38),
% 0.22/0.52    inference(avatar_split_clause,[],[f722,f717,f495,f734])).
% 0.22/0.52  fof(f495,plain,(
% 0.22/0.52    spl16_31 <=> sK9 = k1_relat_1(sK11)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl16_31])])).
% 0.22/0.52  fof(f722,plain,(
% 0.22/0.52    r2_hidden(sK13(sK10,sK11),sK9) | (~spl16_31 | ~spl16_38)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f719,f529])).
% 0.22/0.52  fof(f529,plain,(
% 0.22/0.52    ( ! [X1] : (r2_hidden(sK13(X1,sK11),sK9) | ~sP1(X1,sK11)) ) | ~spl16_31),
% 0.22/0.52    inference(superposition,[],[f71,f497])).
% 0.22/0.52  fof(f497,plain,(
% 0.22/0.52    sK9 = k1_relat_1(sK11) | ~spl16_31),
% 0.22/0.52    inference(avatar_component_clause,[],[f495])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(sK13(X0,X1),k1_relat_1(X1)) | ~sP1(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f37])).
% 0.22/0.52  fof(f742,plain,(
% 0.22/0.52    spl16_41 | ~spl16_38),
% 0.22/0.52    inference(avatar_split_clause,[],[f723,f717,f739])).
% 0.22/0.52  fof(f723,plain,(
% 0.22/0.52    sP0(sK12(sK10,sK11),sK13(sK10,sK11),sK11,sK10) | ~spl16_38),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f719,f72])).
% 0.22/0.52  fof(f720,plain,(
% 0.22/0.52    spl16_38 | spl16_1 | ~spl16_4 | ~spl16_8 | ~spl16_11 | ~spl16_12 | ~spl16_13 | ~spl16_22 | ~spl16_30 | ~spl16_31 | ~spl16_35),
% 0.22/0.52    inference(avatar_split_clause,[],[f713,f606,f495,f487,f370,f177,f172,f159,f144,f124,f109,f717])).
% 0.22/0.52  fof(f109,plain,(
% 0.22/0.52    spl16_1 <=> k2_funct_1(sK10) = sK11),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl16_1])])).
% 0.22/0.52  fof(f124,plain,(
% 0.22/0.52    spl16_4 <=> v2_funct_1(sK10)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl16_4])])).
% 0.22/0.52  fof(f144,plain,(
% 0.22/0.52    spl16_8 <=> v1_funct_1(sK11)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl16_8])])).
% 0.22/0.52  fof(f159,plain,(
% 0.22/0.52    spl16_11 <=> v1_funct_1(sK10)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl16_11])])).
% 0.22/0.52  fof(f172,plain,(
% 0.22/0.52    spl16_12 <=> v1_relat_1(sK10)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl16_12])])).
% 0.22/0.52  fof(f177,plain,(
% 0.22/0.52    spl16_13 <=> v1_relat_1(sK11)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl16_13])])).
% 0.22/0.52  fof(f370,plain,(
% 0.22/0.52    spl16_22 <=> sK9 = k2_relat_1(sK10)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl16_22])])).
% 0.22/0.52  fof(f606,plain,(
% 0.22/0.52    spl16_35 <=> sK8 = k2_relat_1(sK11)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl16_35])])).
% 0.22/0.52  fof(f713,plain,(
% 0.22/0.52    sP1(sK10,sK11) | (spl16_1 | ~spl16_4 | ~spl16_8 | ~spl16_11 | ~spl16_12 | ~spl16_13 | ~spl16_22 | ~spl16_30 | ~spl16_31 | ~spl16_35)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f179,f146,f497,f608,f111,f568])).
% 0.22/0.52  fof(f568,plain,(
% 0.22/0.52    ( ! [X0] : (k2_funct_1(sK10) = X0 | k2_relat_1(X0) != sK8 | sP1(sK10,X0) | k1_relat_1(X0) != sK9 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl16_4 | ~spl16_11 | ~spl16_12 | ~spl16_22 | ~spl16_30)),
% 0.22/0.52    inference(forward_demodulation,[],[f567,f372])).
% 0.22/0.52  fof(f372,plain,(
% 0.22/0.52    sK9 = k2_relat_1(sK10) | ~spl16_22),
% 0.22/0.52    inference(avatar_component_clause,[],[f370])).
% 0.22/0.52  fof(f567,plain,(
% 0.22/0.52    ( ! [X0] : (k2_relat_1(X0) != sK8 | sP1(sK10,X0) | k1_relat_1(X0) != k2_relat_1(sK10) | k2_funct_1(sK10) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl16_4 | ~spl16_11 | ~spl16_12 | ~spl16_30)),
% 0.22/0.52    inference(subsumption_resolution,[],[f566,f174])).
% 0.22/0.52  fof(f174,plain,(
% 0.22/0.52    v1_relat_1(sK10) | ~spl16_12),
% 0.22/0.52    inference(avatar_component_clause,[],[f172])).
% 0.22/0.52  fof(f566,plain,(
% 0.22/0.52    ( ! [X0] : (k2_relat_1(X0) != sK8 | sP1(sK10,X0) | k1_relat_1(X0) != k2_relat_1(sK10) | k2_funct_1(sK10) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK10)) ) | (~spl16_4 | ~spl16_11 | ~spl16_30)),
% 0.22/0.52    inference(subsumption_resolution,[],[f565,f161])).
% 0.22/0.52  fof(f161,plain,(
% 0.22/0.52    v1_funct_1(sK10) | ~spl16_11),
% 0.22/0.52    inference(avatar_component_clause,[],[f159])).
% 0.22/0.52  fof(f565,plain,(
% 0.22/0.52    ( ! [X0] : (k2_relat_1(X0) != sK8 | sP1(sK10,X0) | k1_relat_1(X0) != k2_relat_1(sK10) | k2_funct_1(sK10) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK10) | ~v1_relat_1(sK10)) ) | (~spl16_4 | ~spl16_30)),
% 0.22/0.52    inference(subsumption_resolution,[],[f562,f126])).
% 0.22/0.52  fof(f126,plain,(
% 0.22/0.52    v2_funct_1(sK10) | ~spl16_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f124])).
% 0.22/0.52  fof(f562,plain,(
% 0.22/0.52    ( ! [X0] : (k2_relat_1(X0) != sK8 | sP1(sK10,X0) | k1_relat_1(X0) != k2_relat_1(sK10) | k2_funct_1(sK10) = X0 | ~v2_funct_1(sK10) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK10) | ~v1_relat_1(sK10)) ) | ~spl16_30),
% 0.22/0.52    inference(superposition,[],[f75,f489])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_relat_1(X0) != k2_relat_1(X1) | sP1(X0,X1) | k2_relat_1(X0) != k1_relat_1(X1) | k2_funct_1(X0) = X1 | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | sP1(X0,X1) | k2_relat_1(X0) != k1_relat_1(X1) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(definition_folding,[],[f14,f22,f21])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | ? [X2,X3] : ((k1_funct_1(X0,X2) = X3 <~> k1_funct_1(X1,X3) = X2) & r2_hidden(X3,k1_relat_1(X1)) & r2_hidden(X2,k1_relat_1(X0))) | k2_relat_1(X0) != k1_relat_1(X1) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (? [X2,X3] : ((k1_funct_1(X0,X2) = X3 <~> k1_funct_1(X1,X3) = X2) & (r2_hidden(X3,k1_relat_1(X1)) & r2_hidden(X2,k1_relat_1(X0)))) | k2_relat_1(X0) != k1_relat_1(X1) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2,X3] : ((r2_hidden(X3,k1_relat_1(X1)) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2)) & k2_relat_1(X0) = k1_relat_1(X1) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_1)).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    k2_funct_1(sK10) != sK11 | spl16_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f109])).
% 0.22/0.53  fof(f608,plain,(
% 0.22/0.53    sK8 = k2_relat_1(sK11) | ~spl16_35),
% 0.22/0.53    inference(avatar_component_clause,[],[f606])).
% 0.22/0.53  fof(f146,plain,(
% 0.22/0.53    v1_funct_1(sK11) | ~spl16_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f144])).
% 0.22/0.53  fof(f179,plain,(
% 0.22/0.53    v1_relat_1(sK11) | ~spl16_13),
% 0.22/0.53    inference(avatar_component_clause,[],[f177])).
% 0.22/0.53  fof(f609,plain,(
% 0.22/0.53    spl16_35 | ~spl16_15 | ~spl16_34),
% 0.22/0.53    inference(avatar_split_clause,[],[f601,f591,f193,f606])).
% 0.22/0.53  fof(f193,plain,(
% 0.22/0.53    spl16_15 <=> sP4(sK11)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl16_15])])).
% 0.22/0.53  fof(f591,plain,(
% 0.22/0.53    spl16_34 <=> sP3(sK11,sK8)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl16_34])])).
% 0.22/0.53  fof(f601,plain,(
% 0.22/0.53    sK8 = k2_relat_1(sK11) | (~spl16_15 | ~spl16_34)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f195,f593,f77])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | ~sP3(X0,X1) | ~sP4(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ~sP3(X0,X1)) & (sP3(X0,X1) | k2_relat_1(X0) != X1)) | ~sP4(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> sP3(X0,X1)) | ~sP4(X0))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.22/0.53  fof(f593,plain,(
% 0.22/0.53    sP3(sK11,sK8) | ~spl16_34),
% 0.22/0.53    inference(avatar_component_clause,[],[f591])).
% 0.22/0.53  fof(f195,plain,(
% 0.22/0.53    sP4(sK11) | ~spl16_15),
% 0.22/0.53    inference(avatar_component_clause,[],[f193])).
% 0.22/0.53  fof(f594,plain,(
% 0.22/0.53    spl16_34 | ~spl16_31),
% 0.22/0.53    inference(avatar_split_clause,[],[f589,f495,f591])).
% 0.22/0.53  fof(f589,plain,(
% 0.22/0.53    sP3(sK11,sK8) | ~spl16_31),
% 0.22/0.53    inference(subsumption_resolution,[],[f587,f531])).
% 0.22/0.53  fof(f531,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(sK14(sK11,X0),sK8) | sP3(sK11,X0) | ~r2_hidden(sK14(sK11,X0),X0)) ) | ~spl16_31),
% 0.22/0.53    inference(resolution,[],[f514,f81])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~sP2(sK14(X0,X1),X0) | sP3(X0,X1) | ~r2_hidden(sK14(X0,X1),X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f44])).
% 0.22/0.53  fof(f514,plain,(
% 0.22/0.53    ( ! [X0] : (sP2(X0,sK11) | ~r2_hidden(X0,sK8)) ) | ~spl16_31),
% 0.22/0.53    inference(subsumption_resolution,[],[f507,f98])).
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    ( ! [X5] : (r2_hidden(k1_funct_1(sK10,X5),sK9) | ~r2_hidden(X5,sK8)) )),
% 0.22/0.53    inference(equality_resolution,[],[f64])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ( ! [X4,X5] : (r2_hidden(X4,sK9) | k1_funct_1(sK10,X5) != X4 | ~r2_hidden(X5,sK8)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f507,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(k1_funct_1(sK10,X0),sK9) | sP2(X0,sK11) | ~r2_hidden(X0,sK8)) ) | ~spl16_31),
% 0.22/0.53    inference(backward_demodulation,[],[f229,f497])).
% 0.22/0.53  fof(f229,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(k1_funct_1(sK10,X0),k1_relat_1(sK11)) | sP2(X0,sK11) | ~r2_hidden(X0,sK8)) )),
% 0.22/0.53    inference(superposition,[],[f103,f97])).
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    ( ! [X2,X1] : (sP2(k1_funct_1(X1,X2),X1) | ~r2_hidden(X2,k1_relat_1(X1))) )),
% 0.22/0.53    inference(equality_resolution,[],[f84])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (sP2(X0,X1) | k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f48])).
% 0.22/0.53  fof(f587,plain,(
% 0.22/0.53    r2_hidden(sK14(sK11,sK8),sK8) | sP3(sK11,sK8) | ~spl16_31),
% 0.22/0.53    inference(factoring,[],[f560])).
% 0.22/0.53  fof(f560,plain,(
% 0.22/0.53    ( ! [X2] : (r2_hidden(sK14(sK11,X2),sK8) | sP3(sK11,X2) | r2_hidden(sK14(sK11,X2),X2)) ) | ~spl16_31),
% 0.22/0.53    inference(resolution,[],[f557,f80])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sP2(sK14(X0,X1),X0) | sP3(X0,X1) | r2_hidden(sK14(X0,X1),X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f44])).
% 0.22/0.53  fof(f557,plain,(
% 0.22/0.53    ( ! [X0] : (~sP2(X0,sK11) | r2_hidden(X0,sK8)) ) | ~spl16_31),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f552])).
% 0.22/0.53  fof(f552,plain,(
% 0.22/0.53    ( ! [X0] : (~sP2(X0,sK11) | r2_hidden(X0,sK8) | ~sP2(X0,sK11)) ) | ~spl16_31),
% 0.22/0.53    inference(resolution,[],[f528,f236])).
% 0.22/0.53  fof(f236,plain,(
% 0.22/0.53    ( ! [X4] : (~r2_hidden(sK15(X4,sK11),sK9) | r2_hidden(X4,sK8) | ~sP2(X4,sK11)) )),
% 0.22/0.53    inference(superposition,[],[f100,f83])).
% 0.22/0.53  % (13568)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.53  fof(f100,plain,(
% 0.22/0.53    ( ! [X4] : (r2_hidden(k1_funct_1(sK11,X4),sK8) | ~r2_hidden(X4,sK9)) )),
% 0.22/0.53    inference(equality_resolution,[],[f62])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    ( ! [X4,X5] : (r2_hidden(X5,sK8) | k1_funct_1(sK11,X4) != X5 | ~r2_hidden(X4,sK9)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f528,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(sK15(X0,sK11),sK9) | ~sP2(X0,sK11)) ) | ~spl16_31),
% 0.22/0.53    inference(superposition,[],[f82,f497])).
% 0.22/0.53  fof(f506,plain,(
% 0.22/0.53    spl16_31 | spl16_3 | ~spl16_7 | ~spl16_19 | ~spl16_27),
% 0.22/0.53    inference(avatar_split_clause,[],[f505,f428,f268,f139,f119,f495])).
% 0.22/0.53  fof(f119,plain,(
% 0.22/0.53    spl16_3 <=> k1_xboole_0 = sK8),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl16_3])])).
% 0.22/0.53  fof(f139,plain,(
% 0.22/0.53    spl16_7 <=> v1_funct_2(sK11,sK9,sK8)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl16_7])])).
% 0.22/0.53  fof(f268,plain,(
% 0.22/0.53    spl16_19 <=> sP6(sK9,sK11,sK8)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl16_19])])).
% 0.22/0.53  fof(f428,plain,(
% 0.22/0.53    spl16_27 <=> k1_relat_1(sK11) = k1_relset_1(sK9,sK8,sK11)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl16_27])])).
% 0.22/0.53  fof(f505,plain,(
% 0.22/0.53    sK9 = k1_relat_1(sK11) | (spl16_3 | ~spl16_7 | ~spl16_19 | ~spl16_27)),
% 0.22/0.53    inference(subsumption_resolution,[],[f504,f270])).
% 0.22/0.53  fof(f270,plain,(
% 0.22/0.53    sP6(sK9,sK11,sK8) | ~spl16_19),
% 0.22/0.53    inference(avatar_component_clause,[],[f268])).
% 0.22/0.53  fof(f504,plain,(
% 0.22/0.53    sK9 = k1_relat_1(sK11) | ~sP6(sK9,sK11,sK8) | (spl16_3 | ~spl16_7 | ~spl16_27)),
% 0.22/0.53    inference(subsumption_resolution,[],[f503,f166])).
% 0.22/0.53  fof(f166,plain,(
% 0.22/0.53    ( ! [X0] : (~sP5(X0,sK8)) ) | spl16_3),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f121,f93])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~sP5(X0,X1) | k1_xboole_0 = X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f53])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP5(X0,X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP5(X0,X1))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 0.22/0.53  fof(f121,plain,(
% 0.22/0.53    k1_xboole_0 != sK8 | spl16_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f119])).
% 0.22/0.53  fof(f503,plain,(
% 0.22/0.53    sK9 = k1_relat_1(sK11) | sP5(sK9,sK8) | ~sP6(sK9,sK11,sK8) | (~spl16_7 | ~spl16_27)),
% 0.22/0.53    inference(subsumption_resolution,[],[f471,f141])).
% 0.22/0.53  fof(f141,plain,(
% 0.22/0.53    v1_funct_2(sK11,sK9,sK8) | ~spl16_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f139])).
% 0.22/0.53  fof(f471,plain,(
% 0.22/0.53    sK9 = k1_relat_1(sK11) | ~v1_funct_2(sK11,sK9,sK8) | sP5(sK9,sK8) | ~sP6(sK9,sK11,sK8) | ~spl16_27),
% 0.22/0.53    inference(superposition,[],[f430,f91])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP5(X0,X2) | ~sP6(X0,X1,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f52])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP5(X0,X2) | ~sP6(X0,X1,X2))),
% 0.22/0.53    inference(rectify,[],[f51])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP5(X0,X1) | ~sP6(X0,X2,X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP5(X0,X1) | ~sP6(X0,X2,X1))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).
% 0.22/0.53  fof(f430,plain,(
% 0.22/0.53    k1_relat_1(sK11) = k1_relset_1(sK9,sK8,sK11) | ~spl16_27),
% 0.22/0.53    inference(avatar_component_clause,[],[f428])).
% 0.22/0.53  fof(f502,plain,(
% 0.22/0.53    spl16_30 | spl16_2 | ~spl16_10 | ~spl16_18 | ~spl16_26),
% 0.22/0.53    inference(avatar_split_clause,[],[f501,f423,f263,f154,f114,f487])).
% 0.22/0.53  fof(f114,plain,(
% 0.22/0.53    spl16_2 <=> k1_xboole_0 = sK9),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl16_2])])).
% 0.22/0.53  fof(f154,plain,(
% 0.22/0.53    spl16_10 <=> v1_funct_2(sK10,sK8,sK9)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl16_10])])).
% 0.22/0.53  fof(f263,plain,(
% 0.22/0.53    spl16_18 <=> sP6(sK8,sK10,sK9)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl16_18])])).
% 0.22/0.53  fof(f423,plain,(
% 0.22/0.53    spl16_26 <=> k1_relat_1(sK10) = k1_relset_1(sK8,sK9,sK10)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl16_26])])).
% 0.22/0.53  fof(f501,plain,(
% 0.22/0.53    sK8 = k1_relat_1(sK10) | (spl16_2 | ~spl16_10 | ~spl16_18 | ~spl16_26)),
% 0.22/0.53    inference(subsumption_resolution,[],[f500,f265])).
% 0.22/0.53  fof(f265,plain,(
% 0.22/0.53    sP6(sK8,sK10,sK9) | ~spl16_18),
% 0.22/0.53    inference(avatar_component_clause,[],[f263])).
% 0.22/0.53  fof(f500,plain,(
% 0.22/0.53    sK8 = k1_relat_1(sK10) | ~sP6(sK8,sK10,sK9) | (spl16_2 | ~spl16_10 | ~spl16_26)),
% 0.22/0.53    inference(subsumption_resolution,[],[f499,f165])).
% 0.22/0.53  fof(f165,plain,(
% 0.22/0.53    ( ! [X0] : (~sP5(X0,sK9)) ) | spl16_2),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f116,f93])).
% 0.22/0.53  fof(f116,plain,(
% 0.22/0.53    k1_xboole_0 != sK9 | spl16_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f114])).
% 0.22/0.53  fof(f499,plain,(
% 0.22/0.53    sK8 = k1_relat_1(sK10) | sP5(sK8,sK9) | ~sP6(sK8,sK10,sK9) | (~spl16_10 | ~spl16_26)),
% 0.22/0.53    inference(subsumption_resolution,[],[f470,f156])).
% 0.22/0.53  fof(f156,plain,(
% 0.22/0.53    v1_funct_2(sK10,sK8,sK9) | ~spl16_10),
% 0.22/0.53    inference(avatar_component_clause,[],[f154])).
% 0.22/0.53  fof(f470,plain,(
% 0.22/0.53    sK8 = k1_relat_1(sK10) | ~v1_funct_2(sK10,sK8,sK9) | sP5(sK8,sK9) | ~sP6(sK8,sK10,sK9) | ~spl16_26),
% 0.22/0.53    inference(superposition,[],[f425,f91])).
% 0.22/0.53  fof(f425,plain,(
% 0.22/0.53    k1_relat_1(sK10) = k1_relset_1(sK8,sK9,sK10) | ~spl16_26),
% 0.22/0.53    inference(avatar_component_clause,[],[f423])).
% 0.22/0.53  fof(f431,plain,(
% 0.22/0.53    spl16_27 | ~spl16_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f420,f134,f428])).
% 0.22/0.53  fof(f134,plain,(
% 0.22/0.53    spl16_6 <=> m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK8)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl16_6])])).
% 0.22/0.53  fof(f420,plain,(
% 0.22/0.53    k1_relat_1(sK11) = k1_relset_1(sK9,sK8,sK11) | ~spl16_6),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f136,f88])).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.53  fof(f136,plain,(
% 0.22/0.53    m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK8))) | ~spl16_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f134])).
% 0.22/0.53  fof(f426,plain,(
% 0.22/0.53    spl16_26 | ~spl16_9),
% 0.22/0.53    inference(avatar_split_clause,[],[f421,f149,f423])).
% 0.22/0.53  fof(f149,plain,(
% 0.22/0.53    spl16_9 <=> m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl16_9])])).
% 0.22/0.53  fof(f421,plain,(
% 0.22/0.53    k1_relat_1(sK10) = k1_relset_1(sK8,sK9,sK10) | ~spl16_9),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f151,f88])).
% 0.22/0.53  fof(f151,plain,(
% 0.22/0.53    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) | ~spl16_9),
% 0.22/0.53    inference(avatar_component_clause,[],[f149])).
% 0.22/0.53  fof(f390,plain,(
% 0.22/0.53    spl16_24 | ~spl16_16 | ~spl16_22),
% 0.22/0.53    inference(avatar_split_clause,[],[f385,f370,f199,f387])).
% 0.22/0.53  fof(f199,plain,(
% 0.22/0.53    spl16_16 <=> sP3(sK10,k2_relat_1(sK10))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl16_16])])).
% 0.22/0.53  fof(f385,plain,(
% 0.22/0.53    sP3(sK10,sK9) | (~spl16_16 | ~spl16_22)),
% 0.22/0.53    inference(backward_demodulation,[],[f201,f372])).
% 0.22/0.53  fof(f201,plain,(
% 0.22/0.53    sP3(sK10,k2_relat_1(sK10)) | ~spl16_16),
% 0.22/0.53    inference(avatar_component_clause,[],[f199])).
% 0.22/0.53  % (13567)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.53  fof(f382,plain,(
% 0.22/0.53    spl16_22 | ~spl16_5 | ~spl16_9),
% 0.22/0.53    inference(avatar_split_clause,[],[f381,f149,f129,f370])).
% 0.22/0.53  fof(f129,plain,(
% 0.22/0.53    spl16_5 <=> sK9 = k2_relset_1(sK8,sK9,sK10)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl16_5])])).
% 0.22/0.53  fof(f381,plain,(
% 0.22/0.53    sK9 = k2_relat_1(sK10) | (~spl16_5 | ~spl16_9)),
% 0.22/0.53    inference(subsumption_resolution,[],[f367,f151])).
% 0.22/0.53  fof(f367,plain,(
% 0.22/0.53    sK9 = k2_relat_1(sK10) | ~m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) | ~spl16_5),
% 0.22/0.53    inference(superposition,[],[f131,f87])).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.53  fof(f131,plain,(
% 0.22/0.53    sK9 = k2_relset_1(sK8,sK9,sK10) | ~spl16_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f129])).
% 0.22/0.53  fof(f273,plain,(
% 0.22/0.53    spl16_18 | ~spl16_9),
% 0.22/0.53    inference(avatar_split_clause,[],[f261,f149,f263])).
% 0.22/0.53  fof(f261,plain,(
% 0.22/0.53    sP6(sK8,sK10,sK9) | ~spl16_9),
% 0.22/0.53    inference(resolution,[],[f95,f151])).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP6(X0,X2,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((sP7(X2,X1,X0) & sP6(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(definition_folding,[],[f20,f30,f29,f28])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP7(X2,X1,X0))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(flattening,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.53  fof(f272,plain,(
% 0.22/0.53    spl16_19 | ~spl16_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f260,f134,f268])).
% 0.22/0.53  fof(f260,plain,(
% 0.22/0.53    sP6(sK9,sK11,sK8) | ~spl16_6),
% 0.22/0.53    inference(resolution,[],[f95,f136])).
% 0.22/0.53  fof(f202,plain,(
% 0.22/0.53    spl16_16 | ~spl16_14),
% 0.22/0.53    inference(avatar_split_clause,[],[f197,f187,f199])).
% 0.22/0.53  fof(f187,plain,(
% 0.22/0.53    spl16_14 <=> sP4(sK10)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl16_14])])).
% 0.22/0.53  fof(f197,plain,(
% 0.22/0.53    sP3(sK10,k2_relat_1(sK10)) | ~spl16_14),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f189,f102])).
% 0.22/0.53  fof(f102,plain,(
% 0.22/0.53    ( ! [X0] : (sP3(X0,k2_relat_1(X0)) | ~sP4(X0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f76])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sP3(X0,X1) | k2_relat_1(X0) != X1 | ~sP4(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f40])).
% 0.22/0.53  fof(f189,plain,(
% 0.22/0.53    sP4(sK10) | ~spl16_14),
% 0.22/0.53    inference(avatar_component_clause,[],[f187])).
% 0.22/0.53  fof(f196,plain,(
% 0.22/0.53    spl16_15 | ~spl16_8 | ~spl16_13),
% 0.22/0.53    inference(avatar_split_clause,[],[f191,f177,f144,f193])).
% 0.22/0.53  fof(f191,plain,(
% 0.22/0.53    sP4(sK11) | (~spl16_8 | ~spl16_13)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f146,f179,f85])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    ( ! [X0] : (sP4(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X0] : (sP4(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(definition_folding,[],[f16,f26,f25,f24])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 0.22/0.53  fof(f190,plain,(
% 0.22/0.53    spl16_14 | ~spl16_11 | ~spl16_12),
% 0.22/0.53    inference(avatar_split_clause,[],[f185,f172,f159,f187])).
% 0.22/0.53  fof(f185,plain,(
% 0.22/0.53    sP4(sK10) | (~spl16_11 | ~spl16_12)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f161,f174,f85])).
% 0.22/0.53  fof(f184,plain,(
% 0.22/0.53    spl16_12 | ~spl16_9),
% 0.22/0.53    inference(avatar_split_clause,[],[f183,f149,f172])).
% 0.22/0.53  fof(f183,plain,(
% 0.22/0.53    v1_relat_1(sK10) | ~spl16_9),
% 0.22/0.53    inference(subsumption_resolution,[],[f170,f86])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.53  fof(f170,plain,(
% 0.22/0.53    v1_relat_1(sK10) | ~v1_relat_1(k2_zfmisc_1(sK8,sK9)) | ~spl16_9),
% 0.22/0.53    inference(resolution,[],[f69,f151])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.53  fof(f182,plain,(
% 0.22/0.53    spl16_13 | ~spl16_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f181,f134,f177])).
% 0.22/0.53  fof(f181,plain,(
% 0.22/0.53    v1_relat_1(sK11) | ~spl16_6),
% 0.22/0.53    inference(subsumption_resolution,[],[f169,f86])).
% 0.22/0.53  fof(f169,plain,(
% 0.22/0.53    v1_relat_1(sK11) | ~v1_relat_1(k2_zfmisc_1(sK9,sK8)) | ~spl16_6),
% 0.22/0.53    inference(resolution,[],[f69,f136])).
% 0.22/0.53  fof(f162,plain,(
% 0.22/0.53    spl16_11),
% 0.22/0.53    inference(avatar_split_clause,[],[f54,f159])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    v1_funct_1(sK10)),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f157,plain,(
% 0.22/0.53    spl16_10),
% 0.22/0.53    inference(avatar_split_clause,[],[f55,f154])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    v1_funct_2(sK10,sK8,sK9)),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f152,plain,(
% 0.22/0.53    spl16_9),
% 0.22/0.53    inference(avatar_split_clause,[],[f56,f149])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f147,plain,(
% 0.22/0.53    spl16_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f57,f144])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    v1_funct_1(sK11)),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f142,plain,(
% 0.22/0.53    spl16_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f58,f139])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    v1_funct_2(sK11,sK9,sK8)),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f137,plain,(
% 0.22/0.53    spl16_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f59,f134])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK8)))),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f132,plain,(
% 0.22/0.53    spl16_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f60,f129])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    sK9 = k2_relset_1(sK8,sK9,sK10)),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f127,plain,(
% 0.22/0.53    spl16_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f61,f124])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    v2_funct_1(sK10)),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f122,plain,(
% 0.22/0.53    ~spl16_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f66,f119])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    k1_xboole_0 != sK8),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f117,plain,(
% 0.22/0.53    ~spl16_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f67,f114])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    k1_xboole_0 != sK9),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f112,plain,(
% 0.22/0.53    ~spl16_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f68,f109])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    k2_funct_1(sK10) != sK11),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (13566)------------------------------
% 0.22/0.53  % (13566)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (13566)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (13566)Memory used [KB]: 11513
% 0.22/0.53  % (13566)Time elapsed: 0.096 s
% 0.22/0.53  % (13566)------------------------------
% 0.22/0.53  % (13566)------------------------------
% 0.22/0.53  % (13549)Success in time 0.166 s
%------------------------------------------------------------------------------
