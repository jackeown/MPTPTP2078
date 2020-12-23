%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t170_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:36 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  375 (1100 expanded)
%              Number of leaves         :  103 ( 443 expanded)
%              Depth                    :   19
%              Number of atoms          : 1073 (3047 expanded)
%              Number of equality atoms :   87 ( 322 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f928,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f114,f121,f128,f136,f143,f155,f164,f174,f181,f188,f195,f205,f212,f238,f264,f274,f287,f289,f310,f333,f343,f358,f363,f368,f381,f394,f406,f415,f428,f439,f452,f464,f476,f496,f510,f513,f521,f536,f560,f569,f585,f602,f626,f653,f684,f696,f707,f714,f723,f737,f750,f754,f767,f777,f793,f822,f835,f848,f864,f871,f909,f916,f923,f927])).

fof(f927,plain,
    ( ~ spl7_102
    | ~ spl7_148 ),
    inference(avatar_contradiction_clause,[],[f926])).

fof(f926,plain,
    ( $false
    | ~ spl7_102
    | ~ spl7_148 ),
    inference(subsumption_resolution,[],[f925,f683])).

fof(f683,plain,
    ( m1_subset_1(sK6(sK1,sK2),k9_setfam_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_102 ),
    inference(avatar_component_clause,[],[f682])).

fof(f682,plain,
    ( spl7_102
  <=> m1_subset_1(sK6(sK1,sK2),k9_setfam_1(k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_102])])).

fof(f925,plain,
    ( ~ m1_subset_1(sK6(sK1,sK2),k9_setfam_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_148 ),
    inference(trivial_inequality_removal,[],[f924])).

fof(f924,plain,
    ( k1_funct_1(sK2,sK3(sK6(sK1,sK2))) != k1_funct_1(sK2,sK3(sK6(sK1,sK2)))
    | ~ m1_subset_1(sK6(sK1,sK2),k9_setfam_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_148 ),
    inference(superposition,[],[f88,f922])).

fof(f922,plain,
    ( k11_relat_1(sK6(sK1,sK2),sK3(sK6(sK1,sK2))) = k1_funct_1(sK2,sK3(sK6(sK1,sK2)))
    | ~ spl7_148 ),
    inference(avatar_component_clause,[],[f921])).

fof(f921,plain,
    ( spl7_148
  <=> k11_relat_1(sK6(sK1,sK2),sK3(sK6(sK1,sK2))) = k1_funct_1(sK2,sK3(sK6(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_148])])).

fof(f88,plain,(
    ! [X2] :
      ( k11_relat_1(X2,sK3(X2)) != k1_funct_1(sK2,sK3(X2))
      | ~ m1_subset_1(X2,k9_setfam_1(k2_zfmisc_1(sK1,sK1))) ) ),
    inference(forward_demodulation,[],[f65,f69])).

fof(f69,plain,(
    ! [X0] : k9_setfam_1(X0) = k1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k9_setfam_1(X0) = k1_zfmisc_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t170_funct_2.p',redefinition_k9_setfam_1)).

fof(f65,plain,(
    ! [X2] :
      ( k11_relat_1(X2,sK3(X2)) != k1_funct_1(sK2,sK3(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( ! [X2] :
        ( ( k11_relat_1(X2,sK3(X2)) != k1_funct_1(sK2,sK3(X2))
          & r2_hidden(sK3(X2),sK1) )
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,k9_setfam_1(sK1))))
    & v1_funct_2(sK2,sK1,k9_setfam_1(sK1))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f32,f51,f50])).

fof(f50,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ? [X3] :
                ( k11_relat_1(X2,X3) != k1_funct_1(X1,X3)
                & r2_hidden(X3,X0) )
            | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
        & v1_funct_2(X1,X0,k9_setfam_1(X0))
        & v1_funct_1(X1) )
   => ( ! [X2] :
          ( ? [X3] :
              ( k11_relat_1(X2,X3) != k1_funct_1(sK2,X3)
              & r2_hidden(X3,sK1) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,k9_setfam_1(sK1))))
      & v1_funct_2(sK2,sK1,k9_setfam_1(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( k11_relat_1(X2,X3) != k1_funct_1(X1,X3)
          & r2_hidden(X3,X0) )
     => ( k11_relat_1(X2,sK3(X2)) != k1_funct_1(X1,sK3(X2))
        & r2_hidden(sK3(X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( k11_relat_1(X2,X3) != k1_funct_1(X1,X3)
              & r2_hidden(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      & v1_funct_2(X1,X0,k9_setfam_1(X0))
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( k11_relat_1(X2,X3) != k1_funct_1(X1,X3)
              & r2_hidden(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      & v1_funct_2(X1,X0,k9_setfam_1(X0))
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
          & v1_funct_2(X1,X0,k9_setfam_1(X0))
          & v1_funct_1(X1) )
       => ? [X2] :
            ( ! [X3] :
                ( r2_hidden(X3,X0)
               => k11_relat_1(X2,X3) = k1_funct_1(X1,X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
        & v1_funct_2(X1,X0,k9_setfam_1(X0))
        & v1_funct_1(X1) )
     => ? [X2] :
          ( ! [X3] :
              ( r2_hidden(X3,X0)
             => k11_relat_1(X2,X3) = k1_funct_1(X1,X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t170_funct_2.p',t170_funct_2)).

fof(f923,plain,
    ( spl7_148
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_8
    | spl7_101
    | ~ spl7_104 ),
    inference(avatar_split_clause,[],[f804,f694,f651,f141,f126,f112,f921])).

fof(f112,plain,
    ( spl7_0
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_0])])).

fof(f126,plain,
    ( spl7_4
  <=> v1_funct_2(sK2,sK1,k9_setfam_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f141,plain,
    ( spl7_8
  <=> m1_subset_1(sK2,k9_setfam_1(k2_zfmisc_1(sK1,k9_setfam_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f651,plain,
    ( spl7_101
  <=> ~ sP0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_101])])).

fof(f694,plain,
    ( spl7_104
  <=> r2_hidden(sK3(sK6(sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_104])])).

fof(f804,plain,
    ( k11_relat_1(sK6(sK1,sK2),sK3(sK6(sK1,sK2))) = k1_funct_1(sK2,sK3(sK6(sK1,sK2)))
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_101
    | ~ spl7_104 ),
    inference(resolution,[],[f796,f695])).

fof(f695,plain,
    ( r2_hidden(sK3(sK6(sK1,sK2)),sK1)
    | ~ spl7_104 ),
    inference(avatar_component_clause,[],[f694])).

fof(f796,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | k11_relat_1(sK6(sK1,sK2),X0) = k1_funct_1(sK2,X0) )
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_101 ),
    inference(subsumption_resolution,[],[f795,f127])).

fof(f127,plain,
    ( v1_funct_2(sK2,sK1,k9_setfam_1(sK1))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f126])).

fof(f795,plain,
    ( ! [X0] :
        ( k11_relat_1(sK6(sK1,sK2),X0) = k1_funct_1(sK2,X0)
        | ~ v1_funct_2(sK2,sK1,k9_setfam_1(sK1))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl7_0
    | ~ spl7_8
    | ~ spl7_101 ),
    inference(subsumption_resolution,[],[f794,f652])).

fof(f652,plain,
    ( ~ sP0(sK1,sK2)
    | ~ spl7_101 ),
    inference(avatar_component_clause,[],[f651])).

fof(f794,plain,
    ( ! [X0] :
        ( k11_relat_1(sK6(sK1,sK2),X0) = k1_funct_1(sK2,X0)
        | sP0(sK1,sK2)
        | ~ v1_funct_2(sK2,sK1,k9_setfam_1(sK1))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl7_0
    | ~ spl7_8 ),
    inference(resolution,[],[f561,f142])).

fof(f142,plain,
    ( m1_subset_1(sK2,k9_setfam_1(k2_zfmisc_1(sK1,k9_setfam_1(sK1))))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f141])).

fof(f561,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k9_setfam_1(k2_zfmisc_1(X1,k9_setfam_1(X1))))
        | k11_relat_1(sK6(X1,sK2),X0) = k1_funct_1(sK2,X0)
        | sP0(X1,sK2)
        | ~ v1_funct_2(sK2,X1,k9_setfam_1(X1))
        | ~ r2_hidden(X0,X1) )
    | ~ spl7_0 ),
    inference(resolution,[],[f100,f113])).

fof(f113,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_0 ),
    inference(avatar_component_clause,[],[f112])).

fof(f100,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r2_hidden(X3,X0)
      | k11_relat_1(sK6(X0,X1),X3) = k1_funct_1(X1,X3)
      | sP0(X0,X1)
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ m1_subset_1(X1,k9_setfam_1(k2_zfmisc_1(X0,k9_setfam_1(X0)))) ) ),
    inference(forward_demodulation,[],[f99,f69])).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | k11_relat_1(sK6(X0,X1),X3) = k1_funct_1(X1,X3)
      | sP0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f98,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t170_funct_2.p',t1_subset)).

fof(f98,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | k11_relat_1(sK6(X0,X1),X3) = k1_funct_1(X1,X3)
      | ~ m1_subset_1(X3,X0)
      | sP0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(forward_demodulation,[],[f81,f68])).

fof(f68,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t170_funct_2.p',d4_subset_1)).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( k11_relat_1(sK6(X0,X1),X3) = k1_funct_1(X1,X3)
      | ~ r2_hidden(X3,k2_subset_1(X0))
      | ~ m1_subset_1(X3,X0)
      | sP0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( k11_relat_1(sK6(X0,X1),X3) = k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,k2_subset_1(X0))
            | ~ m1_subset_1(X3,X0) )
        & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X0),k2_subset_1(X0)))) )
      | sP0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f58,f59])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k11_relat_1(X2,X3) = k1_funct_1(X1,X3)
              | ~ r2_hidden(X3,k2_subset_1(X0))
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X0),k2_subset_1(X0)))) )
     => ( ! [X3] :
            ( k11_relat_1(sK6(X0,X1),X3) = k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,k2_subset_1(X0))
            | ~ m1_subset_1(X3,X0) )
        & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X0),k2_subset_1(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( k11_relat_1(X2,X3) = k1_funct_1(X1,X3)
              | ~ r2_hidden(X3,k2_subset_1(X0))
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X0),k2_subset_1(X0)))) )
      | sP0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ? [X3] :
          ( ! [X4] :
              ( k11_relat_1(X3,X4) = k1_funct_1(X1,X4)
              | ~ r2_hidden(X4,k2_subset_1(X0))
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X0),k2_subset_1(X0)))) )
      | sP0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(definition_folding,[],[f39,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k1_funct_1(X1,X2),k2_subset_1(X0))
          & r2_hidden(X2,k2_subset_1(X0))
          & m1_subset_1(X2,X0) )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ? [X3] :
          ( ! [X4] :
              ( k11_relat_1(X3,X4) = k1_funct_1(X1,X4)
              | ~ r2_hidden(X4,k2_subset_1(X0))
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X0),k2_subset_1(X0)))) )
      | ? [X2] :
          ( ~ r1_tarski(k1_funct_1(X1,X2),k2_subset_1(X0))
          & r2_hidden(X2,k2_subset_1(X0))
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ? [X3] :
          ( ! [X4] :
              ( k11_relat_1(X3,X4) = k1_funct_1(X1,X4)
              | ~ r2_hidden(X4,k2_subset_1(X0))
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X0),k2_subset_1(X0)))) )
      | ? [X2] :
          ( ~ r1_tarski(k1_funct_1(X1,X2),k2_subset_1(X0))
          & r2_hidden(X2,k2_subset_1(X0))
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
        & v1_funct_2(X1,X0,k9_setfam_1(X0))
        & v1_funct_1(X1) )
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => ( r2_hidden(X2,k2_subset_1(X0))
             => r1_tarski(k1_funct_1(X1,X2),k2_subset_1(X0)) ) )
       => ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,X0)
               => ( r2_hidden(X4,k2_subset_1(X0))
                 => k11_relat_1(X3,X4) = k1_funct_1(X1,X4) ) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X0),k2_subset_1(X0)))) ) ) ) ),
    inference(rectify,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
        & v1_funct_2(X1,X0,k9_setfam_1(X0))
        & v1_funct_1(X1) )
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => ( r2_hidden(X2,k2_subset_1(X0))
             => r1_tarski(k1_funct_1(X1,X2),k2_subset_1(X0)) ) )
       => ? [X2] :
            ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,k2_subset_1(X0))
                 => k11_relat_1(X2,X3) = k1_funct_1(X1,X3) ) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X0),k2_subset_1(X0)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t170_funct_2.p',s3_relset_1__e2_192__funct_2)).

fof(f916,plain,
    ( spl7_146
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | spl7_101 ),
    inference(avatar_split_clause,[],[f801,f651,f162,f141,f126,f112,f914])).

fof(f914,plain,
    ( spl7_146
  <=> k11_relat_1(sK6(sK1,sK2),sK3(k2_zfmisc_1(sK1,sK1))) = k1_funct_1(sK2,sK3(k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_146])])).

fof(f162,plain,
    ( spl7_12
  <=> r2_hidden(sK3(k2_zfmisc_1(sK1,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f801,plain,
    ( k11_relat_1(sK6(sK1,sK2),sK3(k2_zfmisc_1(sK1,sK1))) = k1_funct_1(sK2,sK3(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_101 ),
    inference(resolution,[],[f796,f163])).

fof(f163,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(sK1,sK1)),sK1)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f162])).

fof(f909,plain,
    ( ~ spl7_141
    | spl7_142
    | spl7_144
    | ~ spl7_124 ),
    inference(avatar_split_clause,[],[f797,f775,f907,f901,f895])).

fof(f895,plain,
    ( spl7_141
  <=> ~ m1_subset_1(k2_zfmisc_1(sK1,sK1),sK4(sK6(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_141])])).

fof(f901,plain,
    ( spl7_142
  <=> v1_xboole_0(k2_zfmisc_1(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_142])])).

fof(f907,plain,
    ( spl7_144
  <=> v1_xboole_0(sK4(sK6(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_144])])).

fof(f775,plain,
    ( spl7_124
  <=> m1_subset_1(sK4(sK6(sK1,sK2)),k2_zfmisc_1(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_124])])).

fof(f797,plain,
    ( v1_xboole_0(sK4(sK6(sK1,sK2)))
    | v1_xboole_0(k2_zfmisc_1(sK1,sK1))
    | ~ m1_subset_1(k2_zfmisc_1(sK1,sK1),sK4(sK6(sK1,sK2)))
    | ~ spl7_124 ),
    inference(resolution,[],[f776,f220])).

fof(f220,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f214,f76])).

fof(f76,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t170_funct_2.p',t2_subset)).

fof(f214,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X3,X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f76,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t170_funct_2.p',antisymmetry_r2_hidden)).

fof(f776,plain,
    ( m1_subset_1(sK4(sK6(sK1,sK2)),k2_zfmisc_1(sK1,sK1))
    | ~ spl7_124 ),
    inference(avatar_component_clause,[],[f775])).

fof(f871,plain,
    ( spl7_138
    | ~ spl7_134 ),
    inference(avatar_split_clause,[],[f857,f846,f869])).

fof(f869,plain,
    ( spl7_138
  <=> m1_subset_1(o_0_0_xboole_0,k9_setfam_1(sK6(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_138])])).

fof(f846,plain,
    ( spl7_134
  <=> o_0_0_xboole_0 = sK4(k9_setfam_1(sK6(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_134])])).

fof(f857,plain,
    ( m1_subset_1(o_0_0_xboole_0,k9_setfam_1(sK6(sK1,sK2)))
    | ~ spl7_134 ),
    inference(superposition,[],[f73,f847])).

fof(f847,plain,
    ( o_0_0_xboole_0 = sK4(k9_setfam_1(sK6(sK1,sK2)))
    | ~ spl7_134 ),
    inference(avatar_component_clause,[],[f846])).

fof(f73,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t170_funct_2.p',existence_m1_subset_1)).

fof(f864,plain,
    ( spl7_136
    | ~ spl7_134 ),
    inference(avatar_split_clause,[],[f855,f846,f862])).

fof(f862,plain,
    ( spl7_136
  <=> r1_tarski(o_0_0_xboole_0,sK6(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_136])])).

fof(f855,plain,
    ( r1_tarski(o_0_0_xboole_0,sK6(sK1,sK2))
    | ~ spl7_134 ),
    inference(superposition,[],[f146,f847])).

fof(f146,plain,(
    ! [X0] : r1_tarski(sK4(k9_setfam_1(X0)),X0) ),
    inference(resolution,[],[f104,f73])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k9_setfam_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f82,f69])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t170_funct_2.p',t3_subset)).

fof(f848,plain,
    ( spl7_134
    | ~ spl7_2
    | ~ spl7_130 ),
    inference(avatar_split_clause,[],[f837,f827,f119,f846])).

fof(f119,plain,
    ( spl7_2
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f827,plain,
    ( spl7_130
  <=> v1_xboole_0(sK4(k9_setfam_1(sK6(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_130])])).

fof(f837,plain,
    ( o_0_0_xboole_0 = sK4(k9_setfam_1(sK6(sK1,sK2)))
    | ~ spl7_2
    | ~ spl7_130 ),
    inference(resolution,[],[f828,f144])).

fof(f144,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl7_2 ),
    inference(resolution,[],[f83,f120])).

fof(f120,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f119])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t170_funct_2.p',t8_boole)).

fof(f828,plain,
    ( v1_xboole_0(sK4(k9_setfam_1(sK6(sK1,sK2))))
    | ~ spl7_130 ),
    inference(avatar_component_clause,[],[f827])).

fof(f835,plain,
    ( spl7_130
    | spl7_132
    | ~ spl7_120 ),
    inference(avatar_split_clause,[],[f799,f752,f833,f827])).

fof(f833,plain,
    ( spl7_132
  <=> m1_subset_1(sK4(sK4(k9_setfam_1(sK6(sK1,sK2)))),k2_zfmisc_1(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_132])])).

fof(f752,plain,
    ( spl7_120
  <=> ! [X0] :
        ( m1_subset_1(X0,k2_zfmisc_1(sK1,sK1))
        | ~ m1_subset_1(X0,sK6(sK1,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_120])])).

fof(f799,plain,
    ( m1_subset_1(sK4(sK4(k9_setfam_1(sK6(sK1,sK2)))),k2_zfmisc_1(sK1,sK1))
    | v1_xboole_0(sK4(k9_setfam_1(sK6(sK1,sK2))))
    | ~ spl7_120 ),
    inference(resolution,[],[f753,f312])).

fof(f312,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(sK4(k9_setfam_1(X0))),X0)
      | v1_xboole_0(sK4(k9_setfam_1(X0))) ) ),
    inference(resolution,[],[f242,f73])).

fof(f242,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,sK4(k9_setfam_1(X1)))
      | v1_xboole_0(sK4(k9_setfam_1(X1)))
      | m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f241,f76])).

fof(f241,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,sK4(k9_setfam_1(X4)))
      | m1_subset_1(X3,X4) ) ),
    inference(resolution,[],[f105,f73])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(forward_demodulation,[],[f85,f69])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t170_funct_2.p',t4_subset)).

fof(f753,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK6(sK1,sK2))
        | m1_subset_1(X0,k2_zfmisc_1(sK1,sK1)) )
    | ~ spl7_120 ),
    inference(avatar_component_clause,[],[f752])).

fof(f822,plain,
    ( spl7_128
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_8
    | spl7_15
    | spl7_101 ),
    inference(avatar_split_clause,[],[f813,f651,f172,f141,f126,f112,f820])).

fof(f820,plain,
    ( spl7_128
  <=> k11_relat_1(sK6(sK1,sK2),sK4(sK1)) = k1_funct_1(sK2,sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_128])])).

fof(f172,plain,
    ( spl7_15
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f813,plain,
    ( k11_relat_1(sK6(sK1,sK2),sK4(sK1)) = k1_funct_1(sK2,sK4(sK1))
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_15
    | ~ spl7_101 ),
    inference(resolution,[],[f806,f73])).

fof(f806,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k11_relat_1(sK6(sK1,sK2),X0) = k1_funct_1(sK2,X0) )
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_15
    | ~ spl7_101 ),
    inference(subsumption_resolution,[],[f805,f173])).

fof(f173,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f172])).

fof(f805,plain,
    ( ! [X0] :
        ( k11_relat_1(sK6(sK1,sK2),X0) = k1_funct_1(sK2,X0)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X0,sK1) )
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_101 ),
    inference(resolution,[],[f796,f76])).

fof(f793,plain,
    ( spl7_126
    | ~ spl7_104
    | ~ spl7_122 ),
    inference(avatar_split_clause,[],[f781,f765,f694,f791])).

fof(f791,plain,
    ( spl7_126
  <=> r2_hidden(sK3(o_0_0_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_126])])).

fof(f765,plain,
    ( spl7_122
  <=> o_0_0_xboole_0 = sK6(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_122])])).

fof(f781,plain,
    ( r2_hidden(sK3(o_0_0_xboole_0),sK1)
    | ~ spl7_104
    | ~ spl7_122 ),
    inference(superposition,[],[f695,f766])).

fof(f766,plain,
    ( o_0_0_xboole_0 = sK6(sK1,sK2)
    | ~ spl7_122 ),
    inference(avatar_component_clause,[],[f765])).

fof(f777,plain,
    ( spl7_124
    | ~ spl7_120 ),
    inference(avatar_split_clause,[],[f768,f752,f775])).

fof(f768,plain,
    ( m1_subset_1(sK4(sK6(sK1,sK2)),k2_zfmisc_1(sK1,sK1))
    | ~ spl7_120 ),
    inference(resolution,[],[f753,f73])).

fof(f767,plain,
    ( spl7_122
    | ~ spl7_2
    | ~ spl7_118 ),
    inference(avatar_split_clause,[],[f756,f748,f119,f765])).

fof(f748,plain,
    ( spl7_118
  <=> v1_xboole_0(sK6(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_118])])).

fof(f756,plain,
    ( o_0_0_xboole_0 = sK6(sK1,sK2)
    | ~ spl7_2
    | ~ spl7_118 ),
    inference(resolution,[],[f749,f144])).

fof(f749,plain,
    ( v1_xboole_0(sK6(sK1,sK2))
    | ~ spl7_118 ),
    inference(avatar_component_clause,[],[f748])).

fof(f754,plain,
    ( spl7_118
    | spl7_120
    | ~ spl7_102 ),
    inference(avatar_split_clause,[],[f724,f682,f752,f748])).

fof(f724,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k2_zfmisc_1(sK1,sK1))
        | v1_xboole_0(sK6(sK1,sK2))
        | ~ m1_subset_1(X0,sK6(sK1,sK2)) )
    | ~ spl7_102 ),
    inference(resolution,[],[f686,f76])).

fof(f686,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK6(sK1,sK2))
        | m1_subset_1(X0,k2_zfmisc_1(sK1,sK1)) )
    | ~ spl7_102 ),
    inference(resolution,[],[f683,f105])).

fof(f750,plain,
    ( ~ spl7_117
    | spl7_118
    | ~ spl7_102 ),
    inference(avatar_split_clause,[],[f689,f682,f748,f742])).

fof(f742,plain,
    ( spl7_117
  <=> ~ m1_subset_1(k9_setfam_1(k2_zfmisc_1(sK1,sK1)),sK6(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_117])])).

fof(f689,plain,
    ( v1_xboole_0(sK6(sK1,sK2))
    | ~ m1_subset_1(k9_setfam_1(k2_zfmisc_1(sK1,sK1)),sK6(sK1,sK2))
    | ~ spl7_102 ),
    inference(subsumption_resolution,[],[f688,f91])).

fof(f91,plain,(
    ! [X0] : ~ v1_xboole_0(k9_setfam_1(X0)) ),
    inference(forward_demodulation,[],[f67,f69])).

fof(f67,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t170_funct_2.p',fc1_subset_1)).

fof(f688,plain,
    ( v1_xboole_0(sK6(sK1,sK2))
    | v1_xboole_0(k9_setfam_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(k9_setfam_1(k2_zfmisc_1(sK1,sK1)),sK6(sK1,sK2))
    | ~ spl7_102 ),
    inference(resolution,[],[f683,f220])).

fof(f737,plain,
    ( spl7_112
    | ~ spl7_115
    | ~ spl7_104 ),
    inference(avatar_split_clause,[],[f697,f694,f735,f729])).

fof(f729,plain,
    ( spl7_112
  <=> v1_xboole_0(sK3(sK6(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_112])])).

fof(f735,plain,
    ( spl7_115
  <=> ~ m1_subset_1(sK1,sK3(sK6(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_115])])).

fof(f697,plain,
    ( ~ m1_subset_1(sK1,sK3(sK6(sK1,sK2)))
    | v1_xboole_0(sK3(sK6(sK1,sK2)))
    | ~ spl7_104 ),
    inference(resolution,[],[f695,f214])).

fof(f723,plain,
    ( spl7_110
    | ~ spl7_102 ),
    inference(avatar_split_clause,[],[f687,f682,f721])).

fof(f721,plain,
    ( spl7_110
  <=> r1_tarski(sK6(sK1,sK2),k2_zfmisc_1(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_110])])).

fof(f687,plain,
    ( r1_tarski(sK6(sK1,sK2),k2_zfmisc_1(sK1,sK1))
    | ~ spl7_102 ),
    inference(resolution,[],[f683,f104])).

fof(f714,plain,
    ( ~ spl7_109
    | ~ spl7_104 ),
    inference(avatar_split_clause,[],[f699,f694,f712])).

fof(f712,plain,
    ( spl7_109
  <=> ~ r2_hidden(sK1,sK3(sK6(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_109])])).

fof(f699,plain,
    ( ~ r2_hidden(sK1,sK3(sK6(sK1,sK2)))
    | ~ spl7_104 ),
    inference(resolution,[],[f695,f74])).

fof(f707,plain,
    ( spl7_106
    | ~ spl7_104 ),
    inference(avatar_split_clause,[],[f698,f694,f705])).

fof(f705,plain,
    ( spl7_106
  <=> m1_subset_1(sK3(sK6(sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_106])])).

fof(f698,plain,
    ( m1_subset_1(sK3(sK6(sK1,sK2)),sK1)
    | ~ spl7_104 ),
    inference(resolution,[],[f695,f75])).

fof(f696,plain,
    ( spl7_104
    | ~ spl7_102 ),
    inference(avatar_split_clause,[],[f685,f682,f694])).

fof(f685,plain,
    ( r2_hidden(sK3(sK6(sK1,sK2)),sK1)
    | ~ spl7_102 ),
    inference(resolution,[],[f683,f89])).

fof(f89,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k9_setfam_1(k2_zfmisc_1(sK1,sK1)))
      | r2_hidden(sK3(X2),sK1) ) ),
    inference(forward_demodulation,[],[f64,f69])).

fof(f64,plain,(
    ! [X2] :
      ( r2_hidden(sK3(X2),sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f684,plain,
    ( spl7_102
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_8
    | spl7_101 ),
    inference(avatar_split_clause,[],[f677,f651,f141,f126,f112,f682])).

fof(f677,plain,
    ( m1_subset_1(sK6(sK1,sK2),k9_setfam_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_101 ),
    inference(subsumption_resolution,[],[f676,f127])).

fof(f676,plain,
    ( ~ v1_funct_2(sK2,sK1,k9_setfam_1(sK1))
    | m1_subset_1(sK6(sK1,sK2),k9_setfam_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_0
    | ~ spl7_8
    | ~ spl7_101 ),
    inference(subsumption_resolution,[],[f675,f652])).

fof(f675,plain,
    ( sP0(sK1,sK2)
    | ~ v1_funct_2(sK2,sK1,k9_setfam_1(sK1))
    | m1_subset_1(sK6(sK1,sK2),k9_setfam_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_0
    | ~ spl7_8 ),
    inference(resolution,[],[f453,f142])).

fof(f453,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k9_setfam_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
        | sP0(X0,sK2)
        | ~ v1_funct_2(sK2,X0,k9_setfam_1(X0))
        | m1_subset_1(sK6(X0,sK2),k9_setfam_1(k2_zfmisc_1(X0,X0))) )
    | ~ spl7_0 ),
    inference(resolution,[],[f103,f113])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | m1_subset_1(sK6(X0,X1),k9_setfam_1(k2_zfmisc_1(X0,X0)))
      | sP0(X0,X1)
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ m1_subset_1(X1,k9_setfam_1(k2_zfmisc_1(X0,k9_setfam_1(X0)))) ) ),
    inference(forward_demodulation,[],[f102,f69])).

fof(f102,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK6(X0,X1),k9_setfam_1(k2_zfmisc_1(X0,X0)))
      | sP0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(forward_demodulation,[],[f101,f68])).

fof(f101,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK6(X0,X1),k9_setfam_1(k2_zfmisc_1(k2_subset_1(X0),k2_subset_1(X0))))
      | sP0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(forward_demodulation,[],[f80,f69])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK6(X0,X1),k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X0),k2_subset_1(X0))))
      | sP0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k9_setfam_1(X0))))
      | ~ v1_funct_2(X1,X0,k9_setfam_1(X0))
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f653,plain,
    ( ~ spl7_101
    | ~ spl7_98 ),
    inference(avatar_split_clause,[],[f646,f600,f651])).

fof(f600,plain,
    ( spl7_98
  <=> ! [X0] :
        ( r2_hidden(k1_funct_1(sK2,X0),k9_setfam_1(sK1))
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_98])])).

fof(f646,plain,
    ( ~ sP0(sK1,sK2)
    | ~ spl7_98 ),
    inference(subsumption_resolution,[],[f645,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(forward_demodulation,[],[f78,f68])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),k2_subset_1(X0))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( ~ r1_tarski(k1_funct_1(X1,sK5(X0,X1)),k2_subset_1(X0))
        & r2_hidden(sK5(X0,X1),k2_subset_1(X0))
        & m1_subset_1(sK5(X0,X1),X0) )
      | ~ sP0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f55,f56])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(k1_funct_1(X1,X2),k2_subset_1(X0))
          & r2_hidden(X2,k2_subset_1(X0))
          & m1_subset_1(X2,X0) )
     => ( ~ r1_tarski(k1_funct_1(X1,sK5(X0,X1)),k2_subset_1(X0))
        & r2_hidden(sK5(X0,X1),k2_subset_1(X0))
        & m1_subset_1(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k1_funct_1(X1,X2),k2_subset_1(X0))
          & r2_hidden(X2,k2_subset_1(X0))
          & m1_subset_1(X2,X0) )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f645,plain,
    ( ~ r2_hidden(sK5(sK1,sK2),sK1)
    | ~ sP0(sK1,sK2)
    | ~ spl7_98 ),
    inference(resolution,[],[f643,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_funct_1(X1,sK5(X0,X1)),X0)
      | ~ sP0(X0,X1) ) ),
    inference(forward_demodulation,[],[f79,f68])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_funct_1(X1,sK5(X0,X1)),k2_subset_1(X0))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f643,plain,
    ( ! [X2] :
        ( r1_tarski(k1_funct_1(sK2,X2),sK1)
        | ~ r2_hidden(X2,sK1) )
    | ~ spl7_98 ),
    inference(resolution,[],[f639,f104])).

fof(f639,plain,
    ( ! [X1] :
        ( m1_subset_1(k1_funct_1(sK2,X1),k9_setfam_1(sK1))
        | ~ r2_hidden(X1,sK1) )
    | ~ spl7_98 ),
    inference(resolution,[],[f601,f75])).

fof(f601,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK2,X0),k9_setfam_1(sK1))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl7_98 ),
    inference(avatar_component_clause,[],[f600])).

fof(f626,plain,
    ( ~ spl7_2
    | ~ spl7_96 ),
    inference(avatar_contradiction_clause,[],[f625])).

fof(f625,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_96 ),
    inference(subsumption_resolution,[],[f613,f120])).

fof(f613,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl7_96 ),
    inference(superposition,[],[f91,f598])).

fof(f598,plain,
    ( k9_setfam_1(sK1) = o_0_0_xboole_0
    | ~ spl7_96 ),
    inference(avatar_component_clause,[],[f597])).

fof(f597,plain,
    ( spl7_96
  <=> k9_setfam_1(sK1) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_96])])).

fof(f602,plain,
    ( spl7_96
    | spl7_98
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f592,f141,f134,f126,f112,f600,f597])).

fof(f134,plain,
    ( spl7_6
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f592,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK2,X0),k9_setfam_1(sK1))
        | ~ r2_hidden(X0,sK1)
        | k9_setfam_1(sK1) = o_0_0_xboole_0 )
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f591,f127])).

fof(f591,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK2,X0),k9_setfam_1(sK1))
        | ~ r2_hidden(X0,sK1)
        | ~ v1_funct_2(sK2,sK1,k9_setfam_1(sK1))
        | k9_setfam_1(sK1) = o_0_0_xboole_0 )
    | ~ spl7_0
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(resolution,[],[f351,f142])).

fof(f351,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK2,k9_setfam_1(k2_zfmisc_1(X2,X1)))
        | r2_hidden(k1_funct_1(sK2,X0),X1)
        | ~ r2_hidden(X0,X2)
        | ~ v1_funct_2(sK2,X2,X1)
        | o_0_0_xboole_0 = X1 )
    | ~ spl7_0
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f350,f135])).

fof(f135,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f134])).

fof(f350,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(k1_funct_1(sK2,X0),X1)
        | k1_xboole_0 = X1
        | ~ r2_hidden(X0,X2)
        | ~ v1_funct_2(sK2,X2,X1)
        | ~ m1_subset_1(sK2,k9_setfam_1(k2_zfmisc_1(X2,X1))) )
    | ~ spl7_0 ),
    inference(resolution,[],[f107,f113])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k9_setfam_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(forward_demodulation,[],[f87,f69])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t170_funct_2.p',t7_funct_2)).

fof(f585,plain,
    ( spl7_92
    | ~ spl7_95
    | ~ spl7_66 ),
    inference(avatar_split_clause,[],[f454,f420,f583,f577])).

fof(f577,plain,
    ( spl7_92
  <=> v1_xboole_0(sK3(sK4(sK4(k9_setfam_1(k9_setfam_1(k2_zfmisc_1(sK1,sK1))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_92])])).

fof(f583,plain,
    ( spl7_95
  <=> ~ m1_subset_1(sK1,sK3(sK4(sK4(k9_setfam_1(k9_setfam_1(k2_zfmisc_1(sK1,sK1))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_95])])).

fof(f420,plain,
    ( spl7_66
  <=> r2_hidden(sK3(sK4(sK4(k9_setfam_1(k9_setfam_1(k2_zfmisc_1(sK1,sK1)))))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).

fof(f454,plain,
    ( ~ m1_subset_1(sK1,sK3(sK4(sK4(k9_setfam_1(k9_setfam_1(k2_zfmisc_1(sK1,sK1)))))))
    | v1_xboole_0(sK3(sK4(sK4(k9_setfam_1(k9_setfam_1(k2_zfmisc_1(sK1,sK1)))))))
    | ~ spl7_66 ),
    inference(resolution,[],[f421,f214])).

fof(f421,plain,
    ( r2_hidden(sK3(sK4(sK4(k9_setfam_1(k9_setfam_1(k2_zfmisc_1(sK1,sK1)))))),sK1)
    | ~ spl7_66 ),
    inference(avatar_component_clause,[],[f420])).

fof(f569,plain,
    ( ~ spl7_91
    | ~ spl7_52
    | spl7_83 ),
    inference(avatar_split_clause,[],[f562,f505,f356,f567])).

fof(f567,plain,
    ( spl7_91
  <=> o_0_0_xboole_0 != sK4(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_91])])).

fof(f356,plain,
    ( spl7_52
  <=> o_0_0_xboole_0 = sK4(k9_setfam_1(k9_setfam_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f505,plain,
    ( spl7_83
  <=> o_0_0_xboole_0 != sK4(sK4(k9_setfam_1(k9_setfam_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_83])])).

fof(f562,plain,
    ( o_0_0_xboole_0 != sK4(o_0_0_xboole_0)
    | ~ spl7_52
    | ~ spl7_83 ),
    inference(superposition,[],[f506,f357])).

fof(f357,plain,
    ( o_0_0_xboole_0 = sK4(k9_setfam_1(k9_setfam_1(o_0_0_xboole_0)))
    | ~ spl7_52 ),
    inference(avatar_component_clause,[],[f356])).

fof(f506,plain,
    ( o_0_0_xboole_0 != sK4(sK4(k9_setfam_1(k9_setfam_1(o_0_0_xboole_0))))
    | ~ spl7_83 ),
    inference(avatar_component_clause,[],[f505])).

fof(f560,plain,
    ( ~ spl7_89
    | ~ spl7_52
    | spl7_79 ),
    inference(avatar_split_clause,[],[f553,f471,f356,f558])).

fof(f558,plain,
    ( spl7_89
  <=> ~ v1_xboole_0(sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_89])])).

fof(f471,plain,
    ( spl7_79
  <=> ~ v1_xboole_0(sK4(sK4(k9_setfam_1(k9_setfam_1(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_79])])).

fof(f553,plain,
    ( ~ v1_xboole_0(sK4(o_0_0_xboole_0))
    | ~ spl7_52
    | ~ spl7_79 ),
    inference(superposition,[],[f472,f357])).

fof(f472,plain,
    ( ~ v1_xboole_0(sK4(sK4(k9_setfam_1(k9_setfam_1(o_0_0_xboole_0)))))
    | ~ spl7_79 ),
    inference(avatar_component_clause,[],[f471])).

fof(f536,plain,
    ( spl7_86
    | ~ spl7_82 ),
    inference(avatar_split_clause,[],[f527,f508,f534])).

fof(f534,plain,
    ( spl7_86
  <=> m1_subset_1(o_0_0_xboole_0,sK4(k9_setfam_1(k9_setfam_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_86])])).

fof(f508,plain,
    ( spl7_82
  <=> o_0_0_xboole_0 = sK4(sK4(k9_setfam_1(k9_setfam_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_82])])).

fof(f527,plain,
    ( m1_subset_1(o_0_0_xboole_0,sK4(k9_setfam_1(k9_setfam_1(o_0_0_xboole_0))))
    | ~ spl7_82 ),
    inference(superposition,[],[f73,f509])).

fof(f509,plain,
    ( o_0_0_xboole_0 = sK4(sK4(k9_setfam_1(k9_setfam_1(o_0_0_xboole_0))))
    | ~ spl7_82 ),
    inference(avatar_component_clause,[],[f508])).

fof(f521,plain,
    ( spl7_84
    | ~ spl7_52 ),
    inference(avatar_split_clause,[],[f484,f356,f519])).

fof(f519,plain,
    ( spl7_84
  <=> m1_subset_1(o_0_0_xboole_0,k9_setfam_1(k9_setfam_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_84])])).

fof(f484,plain,
    ( m1_subset_1(o_0_0_xboole_0,k9_setfam_1(k9_setfam_1(o_0_0_xboole_0)))
    | ~ spl7_52 ),
    inference(superposition,[],[f73,f357])).

fof(f513,plain,(
    ~ spl7_76 ),
    inference(avatar_contradiction_clause,[],[f511])).

fof(f511,plain,
    ( $false
    | ~ spl7_76 ),
    inference(resolution,[],[f469,f73])).

fof(f469,plain,
    ( ! [X0] : ~ m1_subset_1(X0,sK4(sK4(k9_setfam_1(k9_setfam_1(o_0_0_xboole_0)))))
    | ~ spl7_76 ),
    inference(avatar_component_clause,[],[f468])).

fof(f468,plain,
    ( spl7_76
  <=> ! [X0] : ~ m1_subset_1(X0,sK4(sK4(k9_setfam_1(k9_setfam_1(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_76])])).

fof(f510,plain,
    ( spl7_82
    | ~ spl7_2
    | ~ spl7_78 ),
    inference(avatar_split_clause,[],[f498,f474,f119,f508])).

fof(f474,plain,
    ( spl7_78
  <=> v1_xboole_0(sK4(sK4(k9_setfam_1(k9_setfam_1(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).

fof(f498,plain,
    ( o_0_0_xboole_0 = sK4(sK4(k9_setfam_1(k9_setfam_1(o_0_0_xboole_0))))
    | ~ spl7_2
    | ~ spl7_78 ),
    inference(resolution,[],[f475,f144])).

fof(f475,plain,
    ( v1_xboole_0(sK4(sK4(k9_setfam_1(k9_setfam_1(o_0_0_xboole_0)))))
    | ~ spl7_78 ),
    inference(avatar_component_clause,[],[f474])).

fof(f496,plain,
    ( spl7_80
    | ~ spl7_52 ),
    inference(avatar_split_clause,[],[f482,f356,f494])).

fof(f494,plain,
    ( spl7_80
  <=> r1_tarski(o_0_0_xboole_0,k9_setfam_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_80])])).

fof(f482,plain,
    ( r1_tarski(o_0_0_xboole_0,k9_setfam_1(o_0_0_xboole_0))
    | ~ spl7_52 ),
    inference(superposition,[],[f146,f357])).

fof(f476,plain,
    ( spl7_76
    | spl7_78
    | ~ spl7_48 ),
    inference(avatar_split_clause,[],[f359,f335,f474,f468])).

fof(f335,plain,
    ( spl7_48
  <=> ! [X4] : ~ r2_hidden(X4,sK4(sK4(k9_setfam_1(k9_setfam_1(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f359,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK4(sK4(k9_setfam_1(k9_setfam_1(o_0_0_xboole_0)))))
        | ~ m1_subset_1(X0,sK4(sK4(k9_setfam_1(k9_setfam_1(o_0_0_xboole_0))))) )
    | ~ spl7_48 ),
    inference(resolution,[],[f336,f76])).

fof(f336,plain,
    ( ! [X4] : ~ r2_hidden(X4,sK4(sK4(k9_setfam_1(k9_setfam_1(o_0_0_xboole_0)))))
    | ~ spl7_48 ),
    inference(avatar_component_clause,[],[f335])).

fof(f464,plain,
    ( ~ spl7_75
    | ~ spl7_66 ),
    inference(avatar_split_clause,[],[f431,f420,f462])).

fof(f462,plain,
    ( spl7_75
  <=> ~ r2_hidden(sK1,sK3(sK4(sK4(k9_setfam_1(k9_setfam_1(k2_zfmisc_1(sK1,sK1))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_75])])).

fof(f431,plain,
    ( ~ r2_hidden(sK1,sK3(sK4(sK4(k9_setfam_1(k9_setfam_1(k2_zfmisc_1(sK1,sK1)))))))
    | ~ spl7_66 ),
    inference(resolution,[],[f421,f74])).

fof(f452,plain,
    ( spl7_72
    | ~ spl7_2
    | ~ spl7_68 ),
    inference(avatar_split_clause,[],[f441,f426,f119,f450])).

fof(f450,plain,
    ( spl7_72
  <=> o_0_0_xboole_0 = sK4(k9_setfam_1(k9_setfam_1(k2_zfmisc_1(sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_72])])).

fof(f426,plain,
    ( spl7_68
  <=> v1_xboole_0(sK4(k9_setfam_1(k9_setfam_1(k2_zfmisc_1(sK1,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).

fof(f441,plain,
    ( o_0_0_xboole_0 = sK4(k9_setfam_1(k9_setfam_1(k2_zfmisc_1(sK1,sK1))))
    | ~ spl7_2
    | ~ spl7_68 ),
    inference(resolution,[],[f427,f144])).

fof(f427,plain,
    ( v1_xboole_0(sK4(k9_setfam_1(k9_setfam_1(k2_zfmisc_1(sK1,sK1)))))
    | ~ spl7_68 ),
    inference(avatar_component_clause,[],[f426])).

fof(f439,plain,
    ( spl7_70
    | ~ spl7_66 ),
    inference(avatar_split_clause,[],[f430,f420,f437])).

fof(f437,plain,
    ( spl7_70
  <=> m1_subset_1(sK3(sK4(sK4(k9_setfam_1(k9_setfam_1(k2_zfmisc_1(sK1,sK1)))))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).

fof(f430,plain,
    ( m1_subset_1(sK3(sK4(sK4(k9_setfam_1(k9_setfam_1(k2_zfmisc_1(sK1,sK1)))))),sK1)
    | ~ spl7_66 ),
    inference(resolution,[],[f421,f75])).

fof(f428,plain,
    ( spl7_66
    | spl7_68 ),
    inference(avatar_split_clause,[],[f317,f426,f420])).

fof(f317,plain,
    ( v1_xboole_0(sK4(k9_setfam_1(k9_setfam_1(k2_zfmisc_1(sK1,sK1)))))
    | r2_hidden(sK3(sK4(sK4(k9_setfam_1(k9_setfam_1(k2_zfmisc_1(sK1,sK1)))))),sK1) ),
    inference(resolution,[],[f312,f89])).

fof(f415,plain,
    ( ~ spl7_65
    | spl7_33
    | spl7_63 ),
    inference(avatar_split_clause,[],[f408,f404,f259,f413])).

fof(f413,plain,
    ( spl7_65
  <=> ~ m1_subset_1(k2_zfmisc_1(sK1,k9_setfam_1(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_65])])).

fof(f259,plain,
    ( spl7_33
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f404,plain,
    ( spl7_63
  <=> ~ r2_hidden(k2_zfmisc_1(sK1,k9_setfam_1(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).

fof(f408,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK1,k9_setfam_1(sK1)),sK2)
    | ~ spl7_33
    | ~ spl7_63 ),
    inference(subsumption_resolution,[],[f407,f260])).

fof(f260,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f259])).

fof(f407,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(k2_zfmisc_1(sK1,k9_setfam_1(sK1)),sK2)
    | ~ spl7_63 ),
    inference(resolution,[],[f405,f76])).

fof(f405,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK1,k9_setfam_1(sK1)),sK2)
    | ~ spl7_63 ),
    inference(avatar_component_clause,[],[f404])).

fof(f406,plain,
    ( ~ spl7_63
    | ~ spl7_8
    | spl7_43
    | ~ spl7_56 ),
    inference(avatar_split_clause,[],[f399,f366,f305,f141,f404])).

fof(f305,plain,
    ( spl7_43
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK1,k9_setfam_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f366,plain,
    ( spl7_56
  <=> ! [X0] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X0,sK2)
        | ~ m1_subset_1(k2_zfmisc_1(sK1,k9_setfam_1(sK1)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f399,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK1,k9_setfam_1(sK1)),sK2)
    | ~ spl7_8
    | ~ spl7_43
    | ~ spl7_56 ),
    inference(subsumption_resolution,[],[f398,f75])).

fof(f398,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK1,k9_setfam_1(sK1)),sK2)
    | ~ r2_hidden(k2_zfmisc_1(sK1,k9_setfam_1(sK1)),sK2)
    | ~ spl7_8
    | ~ spl7_43
    | ~ spl7_56 ),
    inference(subsumption_resolution,[],[f397,f306])).

fof(f306,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK1,k9_setfam_1(sK1)))
    | ~ spl7_43 ),
    inference(avatar_component_clause,[],[f305])).

fof(f397,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK1,k9_setfam_1(sK1)),sK2)
    | v1_xboole_0(k2_zfmisc_1(sK1,k9_setfam_1(sK1)))
    | ~ r2_hidden(k2_zfmisc_1(sK1,k9_setfam_1(sK1)),sK2)
    | ~ spl7_8
    | ~ spl7_56 ),
    inference(resolution,[],[f367,f240])).

fof(f240,plain,
    ( ! [X2] :
        ( m1_subset_1(X2,k2_zfmisc_1(sK1,k9_setfam_1(sK1)))
        | ~ r2_hidden(X2,sK2) )
    | ~ spl7_8 ),
    inference(resolution,[],[f105,f142])).

fof(f367,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_zfmisc_1(sK1,k9_setfam_1(sK1)),X0)
        | ~ m1_subset_1(X0,sK2)
        | v1_xboole_0(X0) )
    | ~ spl7_56 ),
    inference(avatar_component_clause,[],[f366])).

fof(f394,plain,
    ( spl7_60
    | ~ spl7_2
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f383,f308,f119,f392])).

fof(f392,plain,
    ( spl7_60
  <=> k2_zfmisc_1(sK1,k9_setfam_1(sK1)) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f308,plain,
    ( spl7_42
  <=> v1_xboole_0(k2_zfmisc_1(sK1,k9_setfam_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f383,plain,
    ( k2_zfmisc_1(sK1,k9_setfam_1(sK1)) = o_0_0_xboole_0
    | ~ spl7_2
    | ~ spl7_42 ),
    inference(resolution,[],[f309,f144])).

fof(f309,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK1,k9_setfam_1(sK1)))
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f308])).

fof(f381,plain,
    ( spl7_58
    | ~ spl7_2
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f370,f262,f119,f379])).

fof(f379,plain,
    ( spl7_58
  <=> o_0_0_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).

fof(f262,plain,
    ( spl7_32
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f370,plain,
    ( o_0_0_xboole_0 = sK2
    | ~ spl7_2
    | ~ spl7_32 ),
    inference(resolution,[],[f263,f144])).

fof(f263,plain,
    ( v1_xboole_0(sK2)
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f262])).

fof(f368,plain,
    ( spl7_32
    | spl7_56
    | ~ spl7_54 ),
    inference(avatar_split_clause,[],[f364,f361,f366,f262])).

fof(f361,plain,
    ( spl7_54
  <=> ! [X1] :
        ( v1_xboole_0(X1)
        | ~ r2_hidden(X1,sK2)
        | ~ m1_subset_1(k2_zfmisc_1(sK1,k9_setfam_1(sK1)),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).

fof(f364,plain,
    ( ! [X0] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(k2_zfmisc_1(sK1,k9_setfam_1(sK1)),X0)
        | v1_xboole_0(sK2)
        | ~ m1_subset_1(X0,sK2) )
    | ~ spl7_54 ),
    inference(resolution,[],[f362,f76])).

fof(f362,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK2)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(k2_zfmisc_1(sK1,k9_setfam_1(sK1)),X1) )
    | ~ spl7_54 ),
    inference(avatar_component_clause,[],[f361])).

fof(f363,plain,
    ( spl7_42
    | spl7_54
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f244,f141,f361,f308])).

fof(f244,plain,
    ( ! [X1] :
        ( v1_xboole_0(X1)
        | v1_xboole_0(k2_zfmisc_1(sK1,k9_setfam_1(sK1)))
        | ~ m1_subset_1(k2_zfmisc_1(sK1,k9_setfam_1(sK1)),X1)
        | ~ r2_hidden(X1,sK2) )
    | ~ spl7_8 ),
    inference(resolution,[],[f220,f240])).

fof(f358,plain,
    ( spl7_52
    | ~ spl7_2
    | ~ spl7_50 ),
    inference(avatar_split_clause,[],[f345,f341,f119,f356])).

fof(f341,plain,
    ( spl7_50
  <=> v1_xboole_0(sK4(k9_setfam_1(k9_setfam_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f345,plain,
    ( o_0_0_xboole_0 = sK4(k9_setfam_1(k9_setfam_1(o_0_0_xboole_0)))
    | ~ spl7_2
    | ~ spl7_50 ),
    inference(resolution,[],[f342,f144])).

fof(f342,plain,
    ( v1_xboole_0(sK4(k9_setfam_1(k9_setfam_1(o_0_0_xboole_0))))
    | ~ spl7_50 ),
    inference(avatar_component_clause,[],[f341])).

fof(f343,plain,
    ( spl7_48
    | spl7_50
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f318,f119,f341,f335])).

fof(f318,plain,
    ( ! [X4] :
        ( v1_xboole_0(sK4(k9_setfam_1(k9_setfam_1(o_0_0_xboole_0))))
        | ~ r2_hidden(X4,sK4(sK4(k9_setfam_1(k9_setfam_1(o_0_0_xboole_0))))) )
    | ~ spl7_2 ),
    inference(resolution,[],[f312,f221])).

fof(f221,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k9_setfam_1(o_0_0_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f106,f120])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k9_setfam_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(forward_demodulation,[],[f86,f69])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t170_funct_2.p',t5_subset)).

fof(f333,plain,
    ( ~ spl7_45
    | spl7_46
    | spl7_25 ),
    inference(avatar_split_clause,[],[f217,f210,f331,f325])).

fof(f325,plain,
    ( spl7_45
  <=> ~ m1_subset_1(sK1,sK3(sK4(k9_setfam_1(k2_zfmisc_1(sK1,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f331,plain,
    ( spl7_46
  <=> v1_xboole_0(sK3(sK4(k9_setfam_1(k2_zfmisc_1(sK1,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f210,plain,
    ( spl7_25
  <=> ~ r2_hidden(sK1,sK3(sK4(k9_setfam_1(k2_zfmisc_1(sK1,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f217,plain,
    ( v1_xboole_0(sK3(sK4(k9_setfam_1(k2_zfmisc_1(sK1,sK1)))))
    | ~ m1_subset_1(sK1,sK3(sK4(k9_setfam_1(k2_zfmisc_1(sK1,sK1)))))
    | ~ spl7_25 ),
    inference(resolution,[],[f76,f211])).

fof(f211,plain,
    ( ~ r2_hidden(sK1,sK3(sK4(k9_setfam_1(k2_zfmisc_1(sK1,sK1)))))
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f210])).

fof(f310,plain,
    ( ~ spl7_41
    | spl7_42
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f251,f141,f308,f302])).

fof(f302,plain,
    ( spl7_41
  <=> ~ r2_hidden(k9_setfam_1(k2_zfmisc_1(sK1,k9_setfam_1(sK1))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f251,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK1,k9_setfam_1(sK1)))
    | ~ r2_hidden(k9_setfam_1(k2_zfmisc_1(sK1,k9_setfam_1(sK1))),sK2)
    | ~ spl7_8 ),
    inference(resolution,[],[f249,f240])).

fof(f249,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k9_setfam_1(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f243,f91])).

fof(f243,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(k9_setfam_1(X0))
      | ~ m1_subset_1(k9_setfam_1(X0),X0) ) ),
    inference(resolution,[],[f220,f93])).

fof(f93,plain,(
    ! [X0] : m1_subset_1(X0,k9_setfam_1(X0)) ),
    inference(forward_demodulation,[],[f92,f68])).

fof(f92,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k9_setfam_1(X0)) ),
    inference(forward_demodulation,[],[f70,f69])).

fof(f70,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t170_funct_2.p',dt_k2_subset_1)).

fof(f289,plain,(
    ~ spl7_34 ),
    inference(avatar_contradiction_clause,[],[f288])).

fof(f288,plain,
    ( $false
    | ~ spl7_34 ),
    inference(resolution,[],[f267,f73])).

fof(f267,plain,
    ( ! [X0] : ~ m1_subset_1(X0,sK4(k9_setfam_1(o_0_0_xboole_0)))
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f266])).

fof(f266,plain,
    ( spl7_34
  <=> ! [X0] : ~ m1_subset_1(X0,sK4(k9_setfam_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f287,plain,
    ( spl7_38
    | ~ spl7_2
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f276,f272,f119,f285])).

fof(f285,plain,
    ( spl7_38
  <=> o_0_0_xboole_0 = sK4(k9_setfam_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f272,plain,
    ( spl7_36
  <=> v1_xboole_0(sK4(k9_setfam_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f276,plain,
    ( o_0_0_xboole_0 = sK4(k9_setfam_1(o_0_0_xboole_0))
    | ~ spl7_2
    | ~ spl7_36 ),
    inference(resolution,[],[f273,f144])).

fof(f273,plain,
    ( v1_xboole_0(sK4(k9_setfam_1(o_0_0_xboole_0)))
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f272])).

fof(f274,plain,
    ( spl7_34
    | spl7_36
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f225,f119,f272,f266])).

fof(f225,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK4(k9_setfam_1(o_0_0_xboole_0)))
        | ~ m1_subset_1(X0,sK4(k9_setfam_1(o_0_0_xboole_0))) )
    | ~ spl7_2 ),
    inference(resolution,[],[f223,f76])).

fof(f223,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK4(k9_setfam_1(o_0_0_xboole_0)))
    | ~ spl7_2 ),
    inference(resolution,[],[f221,f73])).

fof(f264,plain,
    ( ~ spl7_31
    | spl7_32
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f250,f141,f262,f256])).

fof(f256,plain,
    ( spl7_31
  <=> ~ m1_subset_1(k9_setfam_1(k2_zfmisc_1(sK1,k9_setfam_1(sK1))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f250,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(k9_setfam_1(k2_zfmisc_1(sK1,k9_setfam_1(sK1))),sK2)
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f245,f91])).

fof(f245,plain,
    ( v1_xboole_0(sK2)
    | v1_xboole_0(k9_setfam_1(k2_zfmisc_1(sK1,k9_setfam_1(sK1))))
    | ~ m1_subset_1(k9_setfam_1(k2_zfmisc_1(sK1,k9_setfam_1(sK1))),sK2)
    | ~ spl7_8 ),
    inference(resolution,[],[f220,f142])).

fof(f238,plain,
    ( ~ spl7_27
    | spl7_28
    | spl7_19 ),
    inference(avatar_split_clause,[],[f216,f186,f236,f230])).

fof(f230,plain,
    ( spl7_27
  <=> ~ m1_subset_1(sK1,sK3(k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f236,plain,
    ( spl7_28
  <=> v1_xboole_0(sK3(k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f186,plain,
    ( spl7_19
  <=> ~ r2_hidden(sK1,sK3(k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f216,plain,
    ( v1_xboole_0(sK3(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK1,sK3(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_19 ),
    inference(resolution,[],[f76,f187])).

fof(f187,plain,
    ( ~ r2_hidden(sK1,sK3(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f186])).

fof(f212,plain,
    ( ~ spl7_25
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f197,f193,f210])).

fof(f193,plain,
    ( spl7_20
  <=> r2_hidden(sK3(sK4(k9_setfam_1(k2_zfmisc_1(sK1,sK1)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f197,plain,
    ( ~ r2_hidden(sK1,sK3(sK4(k9_setfam_1(k2_zfmisc_1(sK1,sK1)))))
    | ~ spl7_20 ),
    inference(resolution,[],[f194,f74])).

fof(f194,plain,
    ( r2_hidden(sK3(sK4(k9_setfam_1(k2_zfmisc_1(sK1,sK1)))),sK1)
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f193])).

fof(f205,plain,
    ( spl7_22
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f196,f193,f203])).

fof(f203,plain,
    ( spl7_22
  <=> m1_subset_1(sK3(sK4(k9_setfam_1(k2_zfmisc_1(sK1,sK1)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f196,plain,
    ( m1_subset_1(sK3(sK4(k9_setfam_1(k2_zfmisc_1(sK1,sK1)))),sK1)
    | ~ spl7_20 ),
    inference(resolution,[],[f194,f75])).

fof(f195,plain,(
    spl7_20 ),
    inference(avatar_split_clause,[],[f156,f193])).

fof(f156,plain,(
    r2_hidden(sK3(sK4(k9_setfam_1(k2_zfmisc_1(sK1,sK1)))),sK1) ),
    inference(resolution,[],[f89,f73])).

fof(f188,plain,
    ( ~ spl7_19
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f166,f162,f186])).

fof(f166,plain,
    ( ~ r2_hidden(sK1,sK3(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_12 ),
    inference(resolution,[],[f163,f74])).

fof(f181,plain,
    ( spl7_16
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f165,f162,f179])).

fof(f179,plain,
    ( spl7_16
  <=> m1_subset_1(sK3(k2_zfmisc_1(sK1,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f165,plain,
    ( m1_subset_1(sK3(k2_zfmisc_1(sK1,sK1)),sK1)
    | ~ spl7_12 ),
    inference(resolution,[],[f163,f75])).

fof(f174,plain,
    ( ~ spl7_15
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f167,f162,f172])).

fof(f167,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl7_12 ),
    inference(resolution,[],[f163,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t170_funct_2.p',t7_boole)).

fof(f164,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f157,f162])).

fof(f157,plain,(
    r2_hidden(sK3(k2_zfmisc_1(sK1,sK1)),sK1) ),
    inference(resolution,[],[f89,f93])).

fof(f155,plain,
    ( spl7_10
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f148,f141,f153])).

fof(f153,plain,
    ( spl7_10
  <=> r1_tarski(sK2,k2_zfmisc_1(sK1,k9_setfam_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f148,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK1,k9_setfam_1(sK1)))
    | ~ spl7_8 ),
    inference(resolution,[],[f104,f142])).

fof(f143,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f90,f141])).

fof(f90,plain,(
    m1_subset_1(sK2,k9_setfam_1(k2_zfmisc_1(sK1,k9_setfam_1(sK1)))) ),
    inference(forward_demodulation,[],[f63,f69])).

fof(f63,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,k9_setfam_1(sK1)))) ),
    inference(cnf_transformation,[],[f52])).

fof(f136,plain,
    ( spl7_6
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f129,f119,f134])).

fof(f129,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl7_2 ),
    inference(resolution,[],[f72,f120])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t170_funct_2.p',t6_boole)).

fof(f128,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f62,f126])).

fof(f62,plain,(
    v1_funct_2(sK2,sK1,k9_setfam_1(sK1)) ),
    inference(cnf_transformation,[],[f52])).

fof(f121,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f66,f119])).

fof(f66,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t170_funct_2.p',dt_o_0_0_xboole_0)).

fof(f114,plain,(
    spl7_0 ),
    inference(avatar_split_clause,[],[f61,f112])).

fof(f61,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
