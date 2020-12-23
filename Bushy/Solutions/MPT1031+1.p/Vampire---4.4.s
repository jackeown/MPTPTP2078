%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t136_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:30 EDT 2019

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :  215 ( 676 expanded)
%              Number of leaves         :   49 ( 253 expanded)
%              Depth                    :   14
%              Number of atoms          :  756 (4223 expanded)
%              Number of equality atoms :   79 (1050 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1896,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f122,f144,f388,f396,f418,f425,f549,f704,f764,f815,f821,f823,f829,f976,f1015,f1032,f1076,f1448,f1493,f1678,f1679,f1681,f1688,f1694,f1709,f1710,f1743,f1895])).

fof(f1895,plain,
    ( ~ spl7_31
    | ~ spl7_37
    | ~ spl7_39
    | ~ spl7_140 ),
    inference(avatar_split_clause,[],[f1894,f1059,f1126,f454,f451])).

fof(f451,plain,
    ( spl7_31
  <=> ~ v1_funct_1(sK5(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f454,plain,
    ( spl7_37
  <=> ~ v1_funct_2(sK5(sK0,sK1,sK2),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f1126,plain,
    ( spl7_39
  <=> ~ m1_subset_1(sK5(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f1059,plain,
    ( spl7_140
  <=> k1_funct_1(sK2,sK3(sK5(sK0,sK1,sK2))) = k1_funct_1(sK5(sK0,sK1,sK2),sK3(sK5(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_140])])).

fof(f1894,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK5(sK0,sK1,sK2),sK0,sK1)
    | ~ v1_funct_1(sK5(sK0,sK1,sK2))
    | ~ spl7_140 ),
    inference(trivial_inequality_removal,[],[f1893])).

fof(f1893,plain,
    ( k1_funct_1(sK2,sK3(sK5(sK0,sK1,sK2))) != k1_funct_1(sK2,sK3(sK5(sK0,sK1,sK2)))
    | ~ m1_subset_1(sK5(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK5(sK0,sK1,sK2),sK0,sK1)
    | ~ v1_funct_1(sK5(sK0,sK1,sK2))
    | ~ spl7_140 ),
    inference(superposition,[],[f68,f1060])).

fof(f1060,plain,
    ( k1_funct_1(sK2,sK3(sK5(sK0,sK1,sK2))) = k1_funct_1(sK5(sK0,sK1,sK2),sK3(sK5(sK0,sK1,sK2)))
    | ~ spl7_140 ),
    inference(avatar_component_clause,[],[f1059])).

fof(f68,plain,(
    ! [X3] :
      ( k1_funct_1(sK2,sK3(X3)) != k1_funct_1(X3,sK3(X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(X3,sK0,sK1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,
    ( ! [X3] :
        ( ( k1_funct_1(sK2,sK3(X3)) != k1_funct_1(X3,sK3(X3))
          & r2_hidden(sK3(X3),k1_relset_1(sK0,sK1,sK2)) )
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(X3,sK0,sK1)
        | ~ v1_funct_1(X3) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f33,f56,f55])).

fof(f55,plain,
    ( ? [X0,X1,X2] :
        ( ! [X3] :
            ( ? [X4] :
                ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            | ~ v1_funct_2(X3,X0,X1)
            | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK2,X4) != k1_funct_1(X3,X4)
              & r2_hidden(X4,k1_relset_1(sK0,sK1,sK2)) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          | ~ v1_funct_2(X3,sK0,sK1)
          | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X2,X0,X1,X3] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
     => ( k1_funct_1(X2,sK3(X3)) != k1_funct_1(X3,sK3(X3))
        & r2_hidden(sK3(X3),k1_relset_1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ~ ( ! [X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X3,X0,X1)
                  & v1_funct_1(X3) )
               => ? [X4] :
                    ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                    & r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
            & ( k1_xboole_0 = X1
             => k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ~ ( ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X3,X0,X1)
                & v1_funct_1(X3) )
             => ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          & ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t136_funct_2.p',t136_funct_2)).

fof(f1743,plain,
    ( ~ spl7_139
    | spl7_140
    | ~ spl7_82
    | ~ spl7_104 ),
    inference(avatar_split_clause,[],[f1741,f524,f457,f1059,f1056])).

fof(f1056,plain,
    ( spl7_139
  <=> ~ r2_hidden(sK3(sK5(sK0,sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_139])])).

fof(f457,plain,
    ( spl7_82
  <=> r2_hidden(sK3(sK5(sK0,sK1,sK2)),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_82])])).

fof(f524,plain,
    ( spl7_104
  <=> ! [X0] :
        ( k1_funct_1(sK2,X0) = k1_funct_1(sK5(sK0,sK1,sK2),X0)
        | ~ m1_subset_1(X0,k1_relat_1(sK2))
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_104])])).

fof(f1741,plain,
    ( k1_funct_1(sK2,sK3(sK5(sK0,sK1,sK2))) = k1_funct_1(sK5(sK0,sK1,sK2),sK3(sK5(sK0,sK1,sK2)))
    | ~ r2_hidden(sK3(sK5(sK0,sK1,sK2)),sK0)
    | ~ spl7_82
    | ~ spl7_104 ),
    inference(resolution,[],[f1699,f525])).

fof(f525,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_relat_1(sK2))
        | k1_funct_1(sK2,X0) = k1_funct_1(sK5(sK0,sK1,sK2),X0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl7_104 ),
    inference(avatar_component_clause,[],[f524])).

fof(f1699,plain,
    ( m1_subset_1(sK3(sK5(sK0,sK1,sK2)),k1_relat_1(sK2))
    | ~ spl7_82 ),
    inference(resolution,[],[f458,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t136_funct_2.p',t1_subset)).

fof(f458,plain,
    ( r2_hidden(sK3(sK5(sK0,sK1,sK2)),k1_relat_1(sK2))
    | ~ spl7_82 ),
    inference(avatar_component_clause,[],[f457])).

fof(f1710,plain,
    ( ~ spl7_139
    | spl7_140
    | ~ spl7_40
    | ~ spl7_82 ),
    inference(avatar_split_clause,[],[f1695,f457,f234,f1059,f1056])).

fof(f234,plain,
    ( spl7_40
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | k1_funct_1(sK2,X0) = k1_funct_1(sK5(sK0,sK1,sK2),X0)
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f1695,plain,
    ( k1_funct_1(sK2,sK3(sK5(sK0,sK1,sK2))) = k1_funct_1(sK5(sK0,sK1,sK2),sK3(sK5(sK0,sK1,sK2)))
    | ~ r2_hidden(sK3(sK5(sK0,sK1,sK2)),sK0)
    | ~ spl7_40
    | ~ spl7_82 ),
    inference(resolution,[],[f458,f235])).

fof(f235,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | k1_funct_1(sK2,X0) = k1_funct_1(sK5(sK0,sK1,sK2),X0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl7_40 ),
    inference(avatar_component_clause,[],[f234])).

fof(f1709,plain,
    ( ~ spl7_82
    | spl7_259 ),
    inference(avatar_contradiction_clause,[],[f1708])).

fof(f1708,plain,
    ( $false
    | ~ spl7_82
    | ~ spl7_259 ),
    inference(subsumption_resolution,[],[f1696,f1693])).

fof(f1693,plain,
    ( ~ m1_subset_1(sK3(sK5(sK0,sK1,sK2)),sK0)
    | ~ spl7_259 ),
    inference(avatar_component_clause,[],[f1692])).

fof(f1692,plain,
    ( spl7_259
  <=> ~ m1_subset_1(sK3(sK5(sK0,sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_259])])).

fof(f1696,plain,
    ( m1_subset_1(sK3(sK5(sK0,sK1,sK2)),sK0)
    | ~ spl7_82 ),
    inference(resolution,[],[f458,f398])).

fof(f398,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK2))
      | m1_subset_1(X1,sK0) ) ),
    inference(resolution,[],[f199,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t136_funct_2.p',t4_subset)).

fof(f199,plain,(
    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) ),
    inference(global_subsumption,[],[f65,f187])).

fof(f187,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f82,f125])).

fof(f125,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f65,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t136_funct_2.p',redefinition_k1_relset_1)).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t136_funct_2.p',dt_k1_relset_1)).

fof(f65,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f57])).

fof(f1694,plain,
    ( ~ spl7_259
    | spl7_8
    | spl7_139 ),
    inference(avatar_split_clause,[],[f1690,f1056,f909,f1692])).

fof(f909,plain,
    ( spl7_8
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f1690,plain,
    ( v1_xboole_0(sK0)
    | ~ m1_subset_1(sK3(sK5(sK0,sK1,sK2)),sK0)
    | ~ spl7_139 ),
    inference(resolution,[],[f1057,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t136_funct_2.p',t2_subset)).

fof(f1057,plain,
    ( ~ r2_hidden(sK3(sK5(sK0,sK1,sK2)),sK0)
    | ~ spl7_139 ),
    inference(avatar_component_clause,[],[f1056])).

fof(f1688,plain,
    ( spl7_76
    | spl7_104
    | ~ spl7_40 ),
    inference(avatar_split_clause,[],[f1682,f234,f524,f431])).

fof(f431,plain,
    ( spl7_76
  <=> v1_xboole_0(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_76])])).

fof(f1682,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,X0) = k1_funct_1(sK5(sK0,sK1,sK2),X0)
        | ~ r2_hidden(X0,sK0)
        | v1_xboole_0(k1_relat_1(sK2))
        | ~ m1_subset_1(X0,k1_relat_1(sK2)) )
    | ~ spl7_40 ),
    inference(resolution,[],[f235,f77])).

fof(f1681,plain,
    ( ~ spl7_69
    | ~ spl7_133
    | ~ spl7_35
    | spl7_40
    | ~ spl7_70 ),
    inference(avatar_split_clause,[],[f1680,f414,f234,f213,f972,f411])).

fof(f411,plain,
    ( spl7_69
  <=> ~ v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_69])])).

fof(f972,plain,
    ( spl7_133
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_133])])).

fof(f213,plain,
    ( spl7_35
  <=> ~ r2_hidden(o_1_1_funct_2(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f414,plain,
    ( spl7_70
  <=> ! [X0] :
        ( r2_hidden(k1_funct_1(sK2,sK6(sK0,sK1,sK2)),X0)
        | ~ v5_relat_1(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).

fof(f1680,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(o_1_1_funct_2(sK1),sK1)
        | k1_funct_1(sK2,X0) = k1_funct_1(sK5(sK0,sK1,sK2),X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(sK2) )
    | ~ spl7_70 ),
    inference(forward_demodulation,[],[f1673,f125])).

fof(f1673,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relset_1(sK0,sK1,sK2))
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(o_1_1_funct_2(sK1),sK1)
        | k1_funct_1(sK2,X0) = k1_funct_1(sK5(sK0,sK1,sK2),X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(sK2) )
    | ~ spl7_70 ),
    inference(resolution,[],[f1083,f106])).

fof(f106,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(k1_funct_1(X2,sK6(X0,X1,X2)),X1)
      | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2))
      | ~ r2_hidden(X4,X0)
      | ~ r2_hidden(o_1_1_funct_2(X1),X1)
      | k1_funct_1(X2,X4) = k1_funct_1(sK5(X0,X1,X2),X4)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X4] :
            ( ( ( k1_funct_1(sK5(X0,X1,X2),X4) = o_1_1_funct_2(X1)
                | r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
              & ( k1_funct_1(X2,X4) = k1_funct_1(sK5(X0,X1,X2),X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
            | ~ r2_hidden(X4,X0) )
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK5(X0,X1,X2),X0,X1)
        & v1_funct_1(sK5(X0,X1,X2)) )
      | ( ( ( ~ r2_hidden(o_1_1_funct_2(X1),X1)
            & ~ r2_hidden(sK6(X0,X1,X2),k1_relset_1(X0,X1,X2)) )
          | ( ~ r2_hidden(k1_funct_1(X2,sK6(X0,X1,X2)),X1)
            & r2_hidden(sK6(X0,X1,X2),k1_relset_1(X0,X1,X2)) ) )
        & r2_hidden(sK6(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f60,f62,f61])).

fof(f61,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ( ( k1_funct_1(X3,X4) = o_1_1_funct_2(X1)
                  | r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
                & ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                  | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ! [X4] :
            ( ( ( k1_funct_1(sK5(X0,X1,X2),X4) = o_1_1_funct_2(X1)
                | r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
              & ( k1_funct_1(X2,X4) = k1_funct_1(sK5(X0,X1,X2),X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
            | ~ r2_hidden(X4,X0) )
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK5(X0,X1,X2),X0,X1)
        & v1_funct_1(sK5(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ( ( ~ r2_hidden(o_1_1_funct_2(X1),X1)
              & ~ r2_hidden(X5,k1_relset_1(X0,X1,X2)) )
            | ( ~ r2_hidden(k1_funct_1(X2,X5),X1)
              & r2_hidden(X5,k1_relset_1(X0,X1,X2)) ) )
          & r2_hidden(X5,X0) )
     => ( ( ( ~ r2_hidden(o_1_1_funct_2(X1),X1)
            & ~ r2_hidden(sK6(X0,X1,X2),k1_relset_1(X0,X1,X2)) )
          | ( ~ r2_hidden(k1_funct_1(X2,sK6(X0,X1,X2)),X1)
            & r2_hidden(sK6(X0,X1,X2),k1_relset_1(X0,X1,X2)) ) )
        & r2_hidden(sK6(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ! [X4] :
              ( ( ( k1_funct_1(X3,X4) = o_1_1_funct_2(X1)
                  | r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
                & ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                  | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      | ? [X5] :
          ( ( ( ~ r2_hidden(o_1_1_funct_2(X1),X1)
              & ~ r2_hidden(X5,k1_relset_1(X0,X1,X2)) )
            | ( ~ r2_hidden(k1_funct_1(X2,X5),X1)
              & r2_hidden(X5,k1_relset_1(X0,X1,X2)) ) )
          & r2_hidden(X5,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ? [X4] :
          ( ! [X5] :
              ( ( ( k1_funct_1(X4,X5) = o_1_1_funct_2(X1)
                  | r2_hidden(X5,k1_relset_1(X0,X1,X2)) )
                & ( k1_funct_1(X2,X5) = k1_funct_1(X4,X5)
                  | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2)) ) )
              | ~ r2_hidden(X5,X0) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X4,X0,X1)
          & v1_funct_1(X4) )
      | ? [X3] :
          ( ( ( ~ r2_hidden(o_1_1_funct_2(X1),X1)
              & ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
            | ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
              & r2_hidden(X3,k1_relset_1(X0,X1,X2)) ) )
          & r2_hidden(X3,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ? [X4] :
          ( ! [X5] :
              ( ( ( k1_funct_1(X4,X5) = o_1_1_funct_2(X1)
                  | r2_hidden(X5,k1_relset_1(X0,X1,X2)) )
                & ( k1_funct_1(X2,X5) = k1_funct_1(X4,X5)
                  | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2)) ) )
              | ~ r2_hidden(X5,X0) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X4,X0,X1)
          & v1_funct_1(X4) )
      | ? [X3] :
          ( ( ( ~ r2_hidden(o_1_1_funct_2(X1),X1)
              & ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
            | ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
              & r2_hidden(X3,k1_relset_1(X0,X1,X2)) ) )
          & r2_hidden(X3,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ( r2_hidden(X3,X0)
           => ( ( ~ r2_hidden(X3,k1_relset_1(X0,X1,X2))
               => r2_hidden(o_1_1_funct_2(X1),X1) )
              & ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
               => r2_hidden(k1_funct_1(X2,X3),X1) ) ) )
       => ? [X4] :
            ( ! [X5] :
                ( r2_hidden(X5,X0)
               => ( ( ~ r2_hidden(X5,k1_relset_1(X0,X1,X2))
                   => k1_funct_1(X4,X5) = o_1_1_funct_2(X1) )
                  & ( r2_hidden(X5,k1_relset_1(X0,X1,X2))
                   => k1_funct_1(X2,X5) = k1_funct_1(X4,X5) ) ) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X4,X0,X1)
            & v1_funct_1(X4) ) ) ) ),
    inference(rectify,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ( r2_hidden(X3,X0)
           => ( ( ~ r2_hidden(X3,k1_relset_1(X0,X1,X2))
               => r2_hidden(o_1_1_funct_2(X1),X1) )
              & ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
               => r2_hidden(k1_funct_1(X2,X3),X1) ) ) )
       => ? [X3] :
            ( ! [X4] :
                ( r2_hidden(X4,X0)
               => ( ( ~ r2_hidden(X4,k1_relset_1(X0,X1,X2))
                   => k1_funct_1(X3,X4) = o_1_1_funct_2(X1) )
                  & ( r2_hidden(X4,k1_relset_1(X0,X1,X2))
                   => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t136_funct_2.p',s5_funct_2__e3_154_1_2__funct_2)).

fof(f1083,plain,
    ( r2_hidden(k1_funct_1(sK2,sK6(sK0,sK1,sK2)),sK1)
    | ~ spl7_70 ),
    inference(resolution,[],[f415,f124])).

fof(f124,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f65,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t136_funct_2.p',cc2_relset_1)).

fof(f415,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(sK2,X0)
        | r2_hidden(k1_funct_1(sK2,sK6(sK0,sK1,sK2)),X0) )
    | ~ spl7_70 ),
    inference(avatar_component_clause,[],[f414])).

fof(f1679,plain,
    ( ~ spl7_69
    | ~ spl7_133
    | spl7_36
    | ~ spl7_35
    | ~ spl7_70 ),
    inference(avatar_split_clause,[],[f1671,f414,f213,f221,f972,f411])).

fof(f221,plain,
    ( spl7_36
  <=> v1_funct_2(sK5(sK0,sK1,sK2),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f1671,plain,
    ( ~ r2_hidden(o_1_1_funct_2(sK1),sK1)
    | v1_funct_2(sK5(sK0,sK1,sK2),sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl7_70 ),
    inference(resolution,[],[f1083,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k1_funct_1(X2,sK6(X0,X1,X2)),X1)
      | ~ r2_hidden(o_1_1_funct_2(X1),X1)
      | v1_funct_2(sK5(X0,X1,X2),X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f1678,plain,
    ( spl7_29
    | ~ spl7_70 ),
    inference(avatar_contradiction_clause,[],[f1669])).

fof(f1669,plain,
    ( $false
    | ~ spl7_29
    | ~ spl7_70 ),
    inference(subsumption_resolution,[],[f203,f1083])).

fof(f203,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK6(sK0,sK1,sK2)),sK1)
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f202])).

fof(f202,plain,
    ( spl7_29
  <=> ~ r2_hidden(k1_funct_1(sK2,sK6(sK0,sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f1493,plain,
    ( ~ spl7_31
    | ~ spl7_37
    | spl7_82
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f1485,f226,f457,f454,f451])).

fof(f226,plain,
    ( spl7_38
  <=> m1_subset_1(sK5(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f1485,plain,
    ( r2_hidden(sK3(sK5(sK0,sK1,sK2)),k1_relat_1(sK2))
    | ~ v1_funct_2(sK5(sK0,sK1,sK2),sK0,sK1)
    | ~ v1_funct_1(sK5(sK0,sK1,sK2))
    | ~ spl7_38 ),
    inference(resolution,[],[f227,f186])).

fof(f186,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | r2_hidden(sK3(X3),k1_relat_1(sK2))
      | ~ v1_funct_2(X3,sK0,sK1)
      | ~ v1_funct_1(X3) ) ),
    inference(backward_demodulation,[],[f125,f67])).

fof(f67,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | r2_hidden(sK3(X3),k1_relset_1(sK0,sK1,sK2))
      | ~ v1_funct_2(X3,sK0,sK1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f227,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f226])).

fof(f1448,plain,(
    ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f1447])).

fof(f1447,plain,
    ( $false
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f143,f333])).

fof(f333,plain,(
    ~ v1_partfun1(sK2,sK0) ),
    inference(global_subsumption,[],[f185,f64,f326])).

fof(f326,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | ~ v1_funct_1(sK2)
    | v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f65,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t136_funct_2.p',cc1_funct_2)).

fof(f64,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f185,plain,(
    ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(global_subsumption,[],[f64,f65,f184])).

fof(f184,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(equality_resolution,[],[f68])).

fof(f143,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl7_6
  <=> v1_partfun1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f1076,plain,
    ( ~ spl7_67
    | ~ spl7_69
    | spl7_70
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f1071,f216,f414,f411,f408])).

fof(f408,plain,
    ( spl7_67
  <=> ~ v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_67])])).

fof(f216,plain,
    ( spl7_32
  <=> r2_hidden(sK6(sK0,sK1,sK2),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f1071,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK2,sK6(sK0,sK1,sK2)),X0)
        | ~ v1_funct_1(sK2)
        | ~ v5_relat_1(sK2,X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_32 ),
    inference(resolution,[],[f217,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(X2))
      | r2_hidden(k1_funct_1(X2,X1),X0)
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v5_relat_1(X2,X0)
        & v1_relat_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => r2_hidden(k1_funct_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t136_funct_2.p',t27_partfun1)).

fof(f217,plain,
    ( r2_hidden(sK6(sK0,sK1,sK2),k1_relat_1(sK2))
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f216])).

fof(f1032,plain,
    ( spl7_30
    | ~ spl7_35
    | spl7_32 ),
    inference(avatar_split_clause,[],[f1031,f216,f213,f205])).

fof(f205,plain,
    ( spl7_30
  <=> v1_funct_1(sK5(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f1031,plain,
    ( r2_hidden(sK6(sK0,sK1,sK2),k1_relat_1(sK2))
    | ~ r2_hidden(o_1_1_funct_2(sK1),sK1)
    | v1_funct_1(sK5(sK0,sK1,sK2)) ),
    inference(global_subsumption,[],[f816])).

fof(f816,plain,
    ( r2_hidden(sK6(sK0,sK1,sK2),k1_relat_1(sK2))
    | ~ r2_hidden(o_1_1_funct_2(sK1),sK1)
    | v1_funct_1(sK5(sK0,sK1,sK2)) ),
    inference(global_subsumption,[],[f64,f65,f803])).

fof(f803,plain,
    ( r2_hidden(sK6(sK0,sK1,sK2),k1_relat_1(sK2))
    | ~ r2_hidden(o_1_1_funct_2(sK1),sK1)
    | v1_funct_1(sK5(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f90,f125])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),k1_relset_1(X0,X1,X2))
      | ~ r2_hidden(o_1_1_funct_2(X1),X1)
      | v1_funct_1(sK5(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f1015,plain,(
    spl7_133 ),
    inference(avatar_contradiction_clause,[],[f1014])).

fof(f1014,plain,
    ( $false
    | ~ spl7_133 ),
    inference(subsumption_resolution,[],[f65,f973])).

fof(f973,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_133 ),
    inference(avatar_component_clause,[],[f972])).

fof(f976,plain,
    ( ~ spl7_69
    | ~ spl7_133
    | ~ spl7_35
    | spl7_32
    | spl7_37 ),
    inference(avatar_split_clause,[],[f975,f454,f216,f213,f972,f411])).

fof(f975,plain,
    ( r2_hidden(sK6(sK0,sK1,sK2),k1_relat_1(sK2))
    | ~ r2_hidden(o_1_1_funct_2(sK1),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl7_37 ),
    inference(forward_demodulation,[],[f970,f125])).

fof(f970,plain,
    ( ~ r2_hidden(o_1_1_funct_2(sK1),sK1)
    | r2_hidden(sK6(sK0,sK1,sK2),k1_relset_1(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl7_37 ),
    inference(resolution,[],[f455,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(sK5(X0,X1,X2),X0,X1)
      | ~ r2_hidden(o_1_1_funct_2(X1),X1)
      | r2_hidden(sK6(X0,X1,X2),k1_relset_1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f455,plain,
    ( ~ v1_funct_2(sK5(sK0,sK1,sK2),sK0,sK1)
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f454])).

fof(f829,plain,
    ( ~ spl7_35
    | spl7_32
    | spl7_40 ),
    inference(avatar_split_clause,[],[f828,f234,f216,f213])).

fof(f828,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK2))
      | r2_hidden(sK6(sK0,sK1,sK2),k1_relat_1(sK2))
      | ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(o_1_1_funct_2(sK1),sK1)
      | k1_funct_1(sK2,X1) = k1_funct_1(sK5(sK0,sK1,sK2),X1) ) ),
    inference(global_subsumption,[],[f597])).

fof(f597,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK2))
      | r2_hidden(sK6(sK0,sK1,sK2),k1_relat_1(sK2))
      | ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(o_1_1_funct_2(sK1),sK1)
      | k1_funct_1(sK2,X1) = k1_funct_1(sK5(sK0,sK1,sK2),X1) ) ),
    inference(global_subsumption,[],[f368])).

fof(f368,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK2))
      | r2_hidden(sK6(sK0,sK1,sK2),k1_relat_1(sK2))
      | ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(o_1_1_funct_2(sK1),sK1)
      | k1_funct_1(sK2,X1) = k1_funct_1(sK5(sK0,sK1,sK2),X1) ) ),
    inference(global_subsumption,[],[f238])).

fof(f238,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK2))
      | r2_hidden(sK6(sK0,sK1,sK2),k1_relat_1(sK2))
      | ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(o_1_1_funct_2(sK1),sK1)
      | k1_funct_1(sK2,X1) = k1_funct_1(sK5(sK0,sK1,sK2),X1) ) ),
    inference(global_subsumption,[],[f64,f65,f237])).

fof(f237,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK2))
      | r2_hidden(sK6(sK0,sK1,sK2),k1_relat_1(sK2))
      | ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(o_1_1_funct_2(sK1),sK1)
      | k1_funct_1(sK2,X1) = k1_funct_1(sK5(sK0,sK1,sK2),X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK2) ) ),
    inference(forward_demodulation,[],[f194,f125])).

fof(f194,plain,(
    ! [X1] :
      ( r2_hidden(sK6(sK0,sK1,sK2),k1_relat_1(sK2))
      | ~ r2_hidden(X1,k1_relset_1(sK0,sK1,sK2))
      | ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(o_1_1_funct_2(sK1),sK1)
      | k1_funct_1(sK2,X1) = k1_funct_1(sK5(sK0,sK1,sK2),X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK2) ) ),
    inference(superposition,[],[f105,f125])).

fof(f105,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),k1_relset_1(X0,X1,X2))
      | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2))
      | ~ r2_hidden(X4,X0)
      | ~ r2_hidden(o_1_1_funct_2(X1),X1)
      | k1_funct_1(X2,X4) = k1_funct_1(sK5(X0,X1,X2),X4)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f823,plain,
    ( spl7_38
    | ~ spl7_35
    | spl7_32 ),
    inference(avatar_split_clause,[],[f822,f216,f213,f226])).

fof(f822,plain,
    ( r2_hidden(sK6(sK0,sK1,sK2),k1_relat_1(sK2))
    | ~ r2_hidden(o_1_1_funct_2(sK1),sK1)
    | m1_subset_1(sK5(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(global_subsumption,[],[f591])).

fof(f591,plain,
    ( r2_hidden(sK6(sK0,sK1,sK2),k1_relat_1(sK2))
    | ~ r2_hidden(o_1_1_funct_2(sK1),sK1)
    | m1_subset_1(sK5(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(global_subsumption,[],[f64,f65,f580])).

fof(f580,plain,
    ( r2_hidden(sK6(sK0,sK1,sK2),k1_relat_1(sK2))
    | ~ r2_hidden(o_1_1_funct_2(sK1),sK1)
    | m1_subset_1(sK5(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f100,f125])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),k1_relset_1(X0,X1,X2))
      | ~ r2_hidden(o_1_1_funct_2(X1),X1)
      | m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f821,plain,
    ( ~ spl7_29
    | spl7_38
    | ~ spl7_33 ),
    inference(avatar_split_clause,[],[f820,f208,f226,f202])).

fof(f208,plain,
    ( spl7_33
  <=> ~ r2_hidden(sK6(sK0,sK1,sK2),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f820,plain,
    ( ~ r2_hidden(sK6(sK0,sK1,sK2),k1_relat_1(sK2))
    | m1_subset_1(sK5(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ r2_hidden(k1_funct_1(sK2,sK6(sK0,sK1,sK2)),sK1) ),
    inference(global_subsumption,[],[f589])).

fof(f589,plain,
    ( ~ r2_hidden(sK6(sK0,sK1,sK2),k1_relat_1(sK2))
    | m1_subset_1(sK5(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ r2_hidden(k1_funct_1(sK2,sK6(sK0,sK1,sK2)),sK1) ),
    inference(global_subsumption,[],[f64,f65,f579])).

fof(f579,plain,
    ( ~ r2_hidden(sK6(sK0,sK1,sK2),k1_relat_1(sK2))
    | m1_subset_1(sK5(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ r2_hidden(k1_funct_1(sK2,sK6(sK0,sK1,sK2)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f99,f125])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1,X2),k1_relset_1(X0,X1,X2))
      | m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK6(X0,X1,X2)),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f815,plain,
    ( ~ spl7_29
    | spl7_30
    | ~ spl7_33 ),
    inference(avatar_split_clause,[],[f814,f208,f205,f202])).

fof(f814,plain,
    ( ~ r2_hidden(sK6(sK0,sK1,sK2),k1_relat_1(sK2))
    | v1_funct_1(sK5(sK0,sK1,sK2))
    | ~ r2_hidden(k1_funct_1(sK2,sK6(sK0,sK1,sK2)),sK1) ),
    inference(global_subsumption,[],[f64,f65,f802])).

fof(f802,plain,
    ( ~ r2_hidden(sK6(sK0,sK1,sK2),k1_relat_1(sK2))
    | v1_funct_1(sK5(sK0,sK1,sK2))
    | ~ r2_hidden(k1_funct_1(sK2,sK6(sK0,sK1,sK2)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f89,f125])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1,X2),k1_relset_1(X0,X1,X2))
      | v1_funct_1(sK5(X0,X1,X2))
      | ~ r2_hidden(k1_funct_1(X2,sK6(X0,X1,X2)),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f764,plain,
    ( ~ spl7_2
    | spl7_9 ),
    inference(avatar_contradiction_clause,[],[f763])).

fof(f763,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f69,f710])).

fof(f710,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl7_2
    | ~ spl7_9 ),
    inference(backward_demodulation,[],[f121,f140])).

fof(f140,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl7_9
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f121,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl7_2
  <=> o_0_0_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f69,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t136_funct_2.p',dt_o_0_0_xboole_0)).

fof(f704,plain,
    ( ~ spl7_32
    | ~ spl7_76 ),
    inference(avatar_contradiction_clause,[],[f701])).

fof(f701,plain,
    ( $false
    | ~ spl7_32
    | ~ spl7_76 ),
    inference(subsumption_resolution,[],[f620,f432])).

fof(f432,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | ~ spl7_76 ),
    inference(avatar_component_clause,[],[f431])).

fof(f620,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK2))
    | ~ spl7_32 ),
    inference(resolution,[],[f217,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t136_funct_2.p',t7_boole)).

fof(f549,plain,
    ( spl7_1
    | ~ spl7_64 ),
    inference(avatar_contradiction_clause,[],[f527])).

fof(f527,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_64 ),
    inference(subsumption_resolution,[],[f118,f516])).

fof(f516,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ spl7_64 ),
    inference(resolution,[],[f387,f115])).

fof(f115,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f72,f70])).

fof(f70,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/funct_2__t136_funct_2.p',d2_xboole_0)).

fof(f72,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t136_funct_2.p',t6_boole)).

fof(f387,plain,
    ( v1_xboole_0(sK1)
    | ~ spl7_64 ),
    inference(avatar_component_clause,[],[f386])).

fof(f386,plain,
    ( spl7_64
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f118,plain,
    ( o_0_0_xboole_0 != sK1
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl7_1
  <=> o_0_0_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f425,plain,(
    spl7_69 ),
    inference(avatar_contradiction_clause,[],[f424])).

fof(f424,plain,
    ( $false
    | ~ spl7_69 ),
    inference(subsumption_resolution,[],[f64,f412])).

fof(f412,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl7_69 ),
    inference(avatar_component_clause,[],[f411])).

fof(f418,plain,(
    spl7_67 ),
    inference(avatar_contradiction_clause,[],[f417])).

fof(f417,plain,
    ( $false
    | ~ spl7_67 ),
    inference(subsumption_resolution,[],[f126,f409])).

fof(f409,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl7_67 ),
    inference(avatar_component_clause,[],[f408])).

fof(f126,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f65,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t136_funct_2.p',cc1_relset_1)).

fof(f396,plain,(
    spl7_63 ),
    inference(avatar_contradiction_clause,[],[f395])).

fof(f395,plain,
    ( $false
    | ~ spl7_63 ),
    inference(resolution,[],[f384,f71])).

fof(f71,plain,(
    ! [X0] : m1_subset_1(o_1_1_funct_2(X0),X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(o_1_1_funct_2(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t136_funct_2.p',dt_o_1_1_funct_2)).

fof(f384,plain,
    ( ~ m1_subset_1(o_1_1_funct_2(sK1),sK1)
    | ~ spl7_63 ),
    inference(avatar_component_clause,[],[f383])).

fof(f383,plain,
    ( spl7_63
  <=> ~ m1_subset_1(o_1_1_funct_2(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).

fof(f388,plain,
    ( ~ spl7_63
    | spl7_64
    | spl7_35 ),
    inference(avatar_split_clause,[],[f381,f213,f386,f383])).

fof(f381,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(o_1_1_funct_2(sK1),sK1)
    | ~ spl7_35 ),
    inference(resolution,[],[f214,f77])).

fof(f214,plain,
    ( ~ r2_hidden(o_1_1_funct_2(sK1),sK1)
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f213])).

fof(f144,plain,
    ( ~ spl7_9
    | spl7_6 ),
    inference(avatar_split_clause,[],[f127,f142,f139])).

fof(f127,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ v1_xboole_0(sK0) ),
    inference(resolution,[],[f65,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_partfun1(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t136_funct_2.p',cc1_partfun1)).

fof(f122,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f114,f120,f117])).

fof(f114,plain,
    ( o_0_0_xboole_0 = sK0
    | o_0_0_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f66,f70,f70])).

fof(f66,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f57])).
%------------------------------------------------------------------------------
