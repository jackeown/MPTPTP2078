%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:21 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :  258 (4763 expanded)
%              Number of leaves         :   31 (1613 expanded)
%              Depth                    :   30
%              Number of atoms          :  939 (32939 expanded)
%              Number of equality atoms :  170 (5264 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1742,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f112,f124,f138,f148,f238,f326,f330,f334,f601,f1056,f1144,f1424,f1452,f1461,f1741])).

fof(f1741,plain,
    ( spl3_7
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(avatar_contradiction_clause,[],[f1740])).

fof(f1740,plain,
    ( $false
    | spl3_7
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f1739,f1661])).

fof(f1661,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f1651,f336])).

fof(f336,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(backward_demodulation,[],[f181,f237])).

fof(f237,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl3_14
  <=> k1_xboole_0 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f181,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0)
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f126,f147])).

fof(f147,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl3_8
  <=> k1_xboole_0 = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f126,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f125,f85])).

fof(f85,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f45,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f45,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f40,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
                & v2_funct_1(X2)
                & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2)
            & v2_funct_1(X2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1) )
   => ( ? [X2] :
          ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2)
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X2] :
        ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2)
        & v2_funct_1(X2)
        & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
      & v2_funct_1(sK2)
      & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                 => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( ( l1_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                 => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).

fof(f125,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f47,f84])).

fof(f84,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f44,f52])).

fof(f44,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f47,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f1651,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(resolution,[],[f1635,f81])).

fof(f81,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f1635,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f1615,f1618])).

fof(f1618,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f679,f147])).

fof(f679,plain,(
    k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f158,f131])).

fof(f131,plain,(
    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(resolution,[],[f128,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f128,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f127,f84])).

fof(f127,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f48,f85])).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f41])).

fof(f158,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(forward_demodulation,[],[f157,f84])).

fof(f157,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(forward_demodulation,[],[f49,f85])).

fof(f49,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f1615,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2))))
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f696,f237])).

fof(f696,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f128,f679])).

fof(f1739,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | spl3_7
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f1594,f1618])).

fof(f1594,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k2_relat_1(sK2),sK2)
    | spl3_7
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f1061,f237])).

fof(f1061,plain,
    ( k2_struct_0(sK0) != k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | spl3_7 ),
    inference(forward_demodulation,[],[f142,f679])).

fof(f142,plain,
    ( k2_struct_0(sK0) != k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl3_7
  <=> k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f1461,plain,
    ( ~ spl3_8
    | ~ spl3_10
    | ~ spl3_13
    | ~ spl3_37 ),
    inference(avatar_contradiction_clause,[],[f1460])).

fof(f1460,plain,
    ( $false
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_13
    | ~ spl3_37 ),
    inference(subsumption_resolution,[],[f1458,f1131])).

fof(f1131,plain,
    ( r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f1130,f248])).

fof(f248,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f46,f233])).

fof(f233,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl3_13
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f46,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f1130,plain,
    ( r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f1122,f1109])).

fof(f1109,plain,
    ( v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0)
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f1092,f1108])).

fof(f1108,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f1090,f147])).

fof(f1090,plain,
    ( k2_struct_0(sK1) = k2_relat_1(k1_xboole_0)
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f679,f233])).

fof(f1092,plain,
    ( v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k2_relat_1(k1_xboole_0))
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f695,f233])).

fof(f695,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f126,f679])).

fof(f1122,plain,
    ( r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(resolution,[],[f1112,f83])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f1112,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f1111,f1108])).

fof(f1111,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(k1_xboole_0))))
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f696,f233])).

fof(f1458,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_13
    | ~ spl3_37 ),
    inference(backward_demodulation,[],[f1196,f1419])).

fof(f1419,plain,
    ( k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0))
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f1417])).

fof(f1417,plain,
    ( spl3_37
  <=> k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f1196,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k1_xboole_0)
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f1136,f1147])).

fof(f1147,plain,
    ( k2_funct_1(k1_xboole_0) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0)
    | ~ spl3_10
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f201,f233])).

fof(f201,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,sK2)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl3_10
  <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f1136,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f1135,f1108])).

fof(f1135,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k2_relat_1(k1_xboole_0),k2_tops_2(k2_relat_1(k1_xboole_0),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(k1_xboole_0),k1_xboole_0)),k1_xboole_0)
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f702,f233])).

fof(f702,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2) ),
    inference(backward_demodulation,[],[f528,f679])).

fof(f528,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) ),
    inference(forward_demodulation,[],[f527,f84])).

fof(f527,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) ),
    inference(forward_demodulation,[],[f51,f85])).

fof(f51,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f1452,plain,
    ( ~ spl3_6
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_13
    | spl3_38 ),
    inference(avatar_contradiction_clause,[],[f1451])).

fof(f1451,plain,
    ( $false
    | ~ spl3_6
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_13
    | spl3_38 ),
    inference(subsumption_resolution,[],[f1450,f255])).

fof(f255,plain,
    ( v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_6
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f123,f233])).

fof(f123,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl3_6
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f1450,plain,
    ( ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_13
    | spl3_38 ),
    inference(subsumption_resolution,[],[f1449,f1146])).

fof(f1146,plain,
    ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0))
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f209,f233])).

fof(f209,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl3_11
  <=> v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f1449,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_12
    | ~ spl3_13
    | spl3_38 ),
    inference(subsumption_resolution,[],[f1448,f1145])).

fof(f1145,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f217,f233])).

fof(f217,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f215])).

fof(f215,plain,
    ( spl3_12
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f1448,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | spl3_38 ),
    inference(resolution,[],[f1423,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f1423,plain,
    ( ~ v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0)
    | spl3_38 ),
    inference(avatar_component_clause,[],[f1421])).

fof(f1421,plain,
    ( spl3_38
  <=> v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f1424,plain,
    ( spl3_37
    | ~ spl3_38
    | ~ spl3_6
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_13
    | spl3_14 ),
    inference(avatar_split_clause,[],[f1415,f235,f231,f215,f207,f121,f1421,f1417])).

fof(f1415,plain,
    ( ~ v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0)
    | k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0))
    | ~ spl3_6
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_13
    | spl3_14 ),
    inference(subsumption_resolution,[],[f1406,f236])).

fof(f236,plain,
    ( k1_xboole_0 != k2_struct_0(sK0)
    | spl3_14 ),
    inference(avatar_component_clause,[],[f235])).

fof(f1406,plain,
    ( ~ v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0)
    | k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0))
    | ~ spl3_6
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(resolution,[],[f1190,f79])).

fof(f79,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f1190,plain,
    ( m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ spl3_6
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f1189,f255])).

fof(f1189,plain,
    ( m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f1179,f1146])).

fof(f1179,plain,
    ( m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(resolution,[],[f1145,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1144,plain,
    ( ~ spl3_8
    | spl3_9
    | ~ spl3_13 ),
    inference(avatar_contradiction_clause,[],[f1143])).

fof(f1143,plain,
    ( $false
    | ~ spl3_8
    | spl3_9
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f1142,f1112])).

fof(f1142,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | spl3_9
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f197,f233])).

fof(f197,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl3_9
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f1056,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_26 ),
    inference(avatar_contradiction_clause,[],[f1055])).

fof(f1055,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f1052,f936])).

fof(f936,plain,
    ( r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | ~ spl3_7 ),
    inference(backward_demodulation,[],[f700,f928])).

fof(f928,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f722,f697])).

fof(f697,plain,(
    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(backward_demodulation,[],[f130,f679])).

fof(f130,plain,(
    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(resolution,[],[f128,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f722,plain,
    ( k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f143,f679])).

fof(f143,plain,
    ( k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f141])).

fof(f700,plain,(
    r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2) ),
    inference(backward_demodulation,[],[f156,f679])).

fof(f156,plain,(
    r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) ),
    inference(subsumption_resolution,[],[f155,f46])).

fof(f155,plain,
    ( r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f136,f126])).

fof(f136,plain,
    ( r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f128,f83])).

fof(f1052,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_26 ),
    inference(backward_demodulation,[],[f985,f1036])).

fof(f1036,plain,
    ( sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f1035,f111])).

fof(f111,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl3_4
  <=> sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f1035,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f1034,f123])).

fof(f1034,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f1033,f937])).

fof(f937,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl3_7 ),
    inference(backward_demodulation,[],[f701,f928])).

fof(f701,plain,(
    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f174,f679])).

fof(f174,plain,(
    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f173,f46])).

fof(f173,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f172,f126])).

fof(f172,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f171,f128])).

fof(f171,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f164,f50])).

fof(f50,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f164,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f161])).

fof(f161,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f72,f158])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | v1_funct_2(k2_funct_1(X2),X1,X0)
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f1033,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f1032,f955])).

fof(f955,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f724,f928])).

fof(f724,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f178,f679])).

fof(f178,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f177,f46])).

fof(f177,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f176,f126])).

fof(f176,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f175,f128])).

fof(f175,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f163,f50])).

fof(f163,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f162])).

fof(f162,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f73,f158])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1032,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f1031,f567])).

fof(f567,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f566])).

fof(f566,plain,
    ( spl3_26
  <=> v2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f1031,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(trivial_inequality_removal,[],[f1024])).

fof(f1024,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(superposition,[],[f74,f997])).

fof(f997,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f990,f105])).

fof(f105,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl3_3
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f990,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_7 ),
    inference(resolution,[],[f955,f61])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f985,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2)
    | ~ spl3_7 ),
    inference(backward_demodulation,[],[f938,f954])).

fof(f954,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f723,f928])).

fof(f723,plain,(
    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(forward_demodulation,[],[f170,f679])).

fof(f170,plain,(
    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f169,f46])).

fof(f169,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f168,f126])).

fof(f168,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f167,f128])).

fof(f167,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f166,f50])).

fof(f166,plain,
    ( ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f159])).

fof(f159,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f74,f158])).

fof(f938,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2)
    | ~ spl3_7 ),
    inference(backward_demodulation,[],[f702,f928])).

fof(f601,plain,
    ( ~ spl3_1
    | spl3_26 ),
    inference(avatar_contradiction_clause,[],[f600])).

fof(f600,plain,
    ( $false
    | ~ spl3_1
    | spl3_26 ),
    inference(subsumption_resolution,[],[f599,f94])).

fof(f94,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f599,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_26 ),
    inference(subsumption_resolution,[],[f598,f46])).

fof(f598,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_26 ),
    inference(subsumption_resolution,[],[f597,f50])).

fof(f597,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_26 ),
    inference(resolution,[],[f568,f55])).

fof(f55,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f568,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | spl3_26 ),
    inference(avatar_component_clause,[],[f566])).

fof(f334,plain,
    ( ~ spl3_9
    | spl3_12
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f333,f145,f215,f195])).

fof(f333,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f332,f46])).

fof(f332,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_1(sK2)
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f331,f181])).

fof(f331,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f319,f50])).

fof(f319,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ spl3_8 ),
    inference(trivial_inequality_removal,[],[f318])).

fof(f318,plain,
    ( k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ spl3_8 ),
    inference(superposition,[],[f73,f179])).

fof(f179,plain,
    ( k1_xboole_0 = k2_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2)
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f158,f147])).

fof(f330,plain,
    ( ~ spl3_9
    | spl3_11
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f329,f145,f207,f195])).

fof(f329,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f328,f46])).

fof(f328,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_1(sK2)
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f327,f181])).

fof(f327,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f320,f50])).

fof(f320,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ spl3_8 ),
    inference(trivial_inequality_removal,[],[f317])).

fof(f317,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ spl3_8 ),
    inference(superposition,[],[f72,f179])).

fof(f326,plain,
    ( ~ spl3_9
    | spl3_10
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f325,f145,f199,f195])).

fof(f325,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f324,f46])).

fof(f324,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_1(sK2)
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f323,f181])).

fof(f323,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f322,f50])).

fof(f322,plain,
    ( ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ spl3_8 ),
    inference(trivial_inequality_removal,[],[f315])).

fof(f315,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ spl3_8 ),
    inference(superposition,[],[f74,f179])).

fof(f238,plain,
    ( spl3_13
    | spl3_14
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f229,f145,f235,f231])).

fof(f229,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 = sK2
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f220,f181])).

fof(f220,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0)
    | k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 = sK2
    | ~ spl3_8 ),
    inference(resolution,[],[f180,f79])).

fof(f180,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f128,f147])).

fof(f148,plain,
    ( spl3_7
    | spl3_8 ),
    inference(avatar_split_clause,[],[f139,f145,f141])).

fof(f139,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f132,f126])).

fof(f132,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k1_xboole_0 = k2_struct_0(sK1)
    | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(resolution,[],[f128,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f138,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f129,f95])).

fof(f95,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f129,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f128,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f124,plain,
    ( ~ spl3_1
    | spl3_6 ),
    inference(avatar_split_clause,[],[f119,f121,f93])).

fof(f119,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f90,f46])).

fof(f90,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f50,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f112,plain,
    ( ~ spl3_1
    | spl3_4 ),
    inference(avatar_split_clause,[],[f107,f109,f93])).

fof(f107,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f88,f46])).

fof(f88,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f50,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(f106,plain,
    ( ~ spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f101,f103,f93])).

fof(f101,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f87,f46])).

fof(f87,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f50,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:51:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.47  % (11402)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.49  % (11403)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.50  % (11424)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.51  % (11416)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.51  % (11406)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.51  % (11408)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.51  % (11410)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.51  % (11401)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.51  % (11418)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.52  % (11413)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.52  % (11415)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.52  % (11420)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.52  % (11404)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.52  % (11421)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.53  % (11414)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (11423)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.53  % (11409)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.53  % (11405)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.53  % (11407)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.29/0.53  % (11425)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.29/0.53  % (11411)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.29/0.54  % (11412)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.29/0.54  % (11417)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.29/0.55  % (11426)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.29/0.55  % (11422)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.46/0.55  % (11419)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.46/0.56  % (11402)Refutation found. Thanks to Tanya!
% 1.46/0.56  % SZS status Theorem for theBenchmark
% 1.46/0.56  % SZS output start Proof for theBenchmark
% 1.46/0.56  fof(f1742,plain,(
% 1.46/0.56    $false),
% 1.46/0.56    inference(avatar_sat_refutation,[],[f106,f112,f124,f138,f148,f238,f326,f330,f334,f601,f1056,f1144,f1424,f1452,f1461,f1741])).
% 1.46/0.56  fof(f1741,plain,(
% 1.46/0.56    spl3_7 | ~spl3_8 | ~spl3_14),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f1740])).
% 1.46/0.56  fof(f1740,plain,(
% 1.46/0.56    $false | (spl3_7 | ~spl3_8 | ~spl3_14)),
% 1.46/0.56    inference(subsumption_resolution,[],[f1739,f1661])).
% 1.46/0.56  fof(f1661,plain,(
% 1.46/0.56    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl3_8 | ~spl3_14)),
% 1.46/0.56    inference(subsumption_resolution,[],[f1651,f336])).
% 1.46/0.56  fof(f336,plain,(
% 1.46/0.56    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl3_8 | ~spl3_14)),
% 1.46/0.56    inference(backward_demodulation,[],[f181,f237])).
% 1.46/0.56  fof(f237,plain,(
% 1.46/0.56    k1_xboole_0 = k2_struct_0(sK0) | ~spl3_14),
% 1.46/0.56    inference(avatar_component_clause,[],[f235])).
% 1.46/0.56  fof(f235,plain,(
% 1.46/0.56    spl3_14 <=> k1_xboole_0 = k2_struct_0(sK0)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 1.46/0.56  fof(f181,plain,(
% 1.46/0.56    v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) | ~spl3_8),
% 1.46/0.56    inference(backward_demodulation,[],[f126,f147])).
% 1.46/0.56  fof(f147,plain,(
% 1.46/0.56    k1_xboole_0 = k2_struct_0(sK1) | ~spl3_8),
% 1.46/0.56    inference(avatar_component_clause,[],[f145])).
% 1.46/0.56  fof(f145,plain,(
% 1.46/0.56    spl3_8 <=> k1_xboole_0 = k2_struct_0(sK1)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.46/0.56  fof(f126,plain,(
% 1.46/0.56    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 1.46/0.56    inference(forward_demodulation,[],[f125,f85])).
% 1.46/0.56  fof(f85,plain,(
% 1.46/0.56    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 1.46/0.56    inference(resolution,[],[f45,f52])).
% 1.46/0.56  fof(f52,plain,(
% 1.46/0.56    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f18])).
% 1.46/0.56  fof(f18,plain,(
% 1.46/0.56    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.46/0.56    inference(ennf_transformation,[],[f10])).
% 1.46/0.56  fof(f10,axiom,(
% 1.46/0.56    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 1.46/0.56  fof(f45,plain,(
% 1.46/0.56    l1_struct_0(sK1)),
% 1.46/0.56    inference(cnf_transformation,[],[f41])).
% 1.46/0.56  fof(f41,plain,(
% 1.46/0.56    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 1.46/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f40,f39,f38])).
% 1.46/0.56  fof(f38,plain,(
% 1.46/0.56    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 1.46/0.56    introduced(choice_axiom,[])).
% 1.46/0.56  fof(f39,plain,(
% 1.46/0.56    ? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))),
% 1.46/0.56    introduced(choice_axiom,[])).
% 1.46/0.56  fof(f40,plain,(
% 1.46/0.56    ? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 1.46/0.56    introduced(choice_axiom,[])).
% 1.46/0.56  fof(f17,plain,(
% 1.46/0.56    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 1.46/0.56    inference(flattening,[],[f16])).
% 1.46/0.56  fof(f16,plain,(
% 1.46/0.56    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 1.46/0.56    inference(ennf_transformation,[],[f15])).
% 1.46/0.56  fof(f15,plain,(
% 1.46/0.56    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 1.46/0.56    inference(pure_predicate_removal,[],[f14])).
% 1.46/0.56  fof(f14,negated_conjecture,(
% 1.46/0.56    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 1.46/0.56    inference(negated_conjecture,[],[f13])).
% 1.46/0.56  fof(f13,conjecture,(
% 1.46/0.56    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).
% 1.46/0.56  fof(f125,plain,(
% 1.46/0.56    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))),
% 1.46/0.56    inference(backward_demodulation,[],[f47,f84])).
% 1.46/0.56  fof(f84,plain,(
% 1.46/0.56    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.46/0.56    inference(resolution,[],[f44,f52])).
% 1.46/0.56  fof(f44,plain,(
% 1.46/0.56    l1_struct_0(sK0)),
% 1.46/0.56    inference(cnf_transformation,[],[f41])).
% 1.46/0.56  fof(f47,plain,(
% 1.46/0.56    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.46/0.56    inference(cnf_transformation,[],[f41])).
% 1.46/0.56  fof(f1651,plain,(
% 1.46/0.56    ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl3_8 | ~spl3_14)),
% 1.46/0.56    inference(resolution,[],[f1635,f81])).
% 1.46/0.56  fof(f81,plain,(
% 1.46/0.56    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)) )),
% 1.46/0.56    inference(equality_resolution,[],[f63])).
% 1.46/0.56  fof(f63,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.46/0.56    inference(cnf_transformation,[],[f42])).
% 1.46/0.56  fof(f42,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.56    inference(nnf_transformation,[],[f29])).
% 1.46/0.56  fof(f29,plain,(
% 1.46/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.56    inference(flattening,[],[f28])).
% 1.46/0.56  fof(f28,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.56    inference(ennf_transformation,[],[f7])).
% 1.46/0.56  fof(f7,axiom,(
% 1.46/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.46/0.56  fof(f1635,plain,(
% 1.46/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl3_8 | ~spl3_14)),
% 1.46/0.56    inference(forward_demodulation,[],[f1615,f1618])).
% 1.46/0.56  fof(f1618,plain,(
% 1.46/0.56    k1_xboole_0 = k2_relat_1(sK2) | ~spl3_8),
% 1.46/0.56    inference(forward_demodulation,[],[f679,f147])).
% 1.46/0.56  fof(f679,plain,(
% 1.46/0.56    k2_struct_0(sK1) = k2_relat_1(sK2)),
% 1.46/0.56    inference(backward_demodulation,[],[f158,f131])).
% 1.46/0.56  fof(f131,plain,(
% 1.46/0.56    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.46/0.56    inference(resolution,[],[f128,f61])).
% 1.46/0.56  fof(f61,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f27])).
% 1.46/0.56  fof(f27,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.56    inference(ennf_transformation,[],[f6])).
% 1.46/0.56  fof(f6,axiom,(
% 1.46/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.46/0.56  fof(f128,plain,(
% 1.46/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 1.46/0.56    inference(forward_demodulation,[],[f127,f84])).
% 1.46/0.56  fof(f127,plain,(
% 1.46/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))),
% 1.46/0.56    inference(forward_demodulation,[],[f48,f85])).
% 1.46/0.56  fof(f48,plain,(
% 1.46/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.46/0.56    inference(cnf_transformation,[],[f41])).
% 1.46/0.56  fof(f158,plain,(
% 1.46/0.56    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.46/0.56    inference(forward_demodulation,[],[f157,f84])).
% 1.46/0.56  fof(f157,plain,(
% 1.46/0.56    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.46/0.56    inference(forward_demodulation,[],[f49,f85])).
% 1.46/0.56  fof(f49,plain,(
% 1.46/0.56    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 1.46/0.56    inference(cnf_transformation,[],[f41])).
% 1.46/0.56  fof(f1615,plain,(
% 1.46/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2)))) | ~spl3_14),
% 1.46/0.56    inference(forward_demodulation,[],[f696,f237])).
% 1.46/0.56  fof(f696,plain,(
% 1.46/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 1.46/0.56    inference(backward_demodulation,[],[f128,f679])).
% 1.46/0.56  fof(f1739,plain,(
% 1.46/0.56    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (spl3_7 | ~spl3_8 | ~spl3_14)),
% 1.46/0.56    inference(forward_demodulation,[],[f1594,f1618])).
% 1.46/0.56  fof(f1594,plain,(
% 1.46/0.56    k1_xboole_0 != k1_relset_1(k1_xboole_0,k2_relat_1(sK2),sK2) | (spl3_7 | ~spl3_14)),
% 1.46/0.56    inference(forward_demodulation,[],[f1061,f237])).
% 1.46/0.56  fof(f1061,plain,(
% 1.46/0.56    k2_struct_0(sK0) != k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | spl3_7),
% 1.46/0.56    inference(forward_demodulation,[],[f142,f679])).
% 1.46/0.56  fof(f142,plain,(
% 1.46/0.56    k2_struct_0(sK0) != k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | spl3_7),
% 1.46/0.56    inference(avatar_component_clause,[],[f141])).
% 1.46/0.56  fof(f141,plain,(
% 1.46/0.56    spl3_7 <=> k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.46/0.56  fof(f1461,plain,(
% 1.46/0.56    ~spl3_8 | ~spl3_10 | ~spl3_13 | ~spl3_37),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f1460])).
% 1.46/0.56  fof(f1460,plain,(
% 1.46/0.56    $false | (~spl3_8 | ~spl3_10 | ~spl3_13 | ~spl3_37)),
% 1.46/0.56    inference(subsumption_resolution,[],[f1458,f1131])).
% 1.46/0.56  fof(f1131,plain,(
% 1.46/0.56    r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl3_8 | ~spl3_13)),
% 1.46/0.56    inference(subsumption_resolution,[],[f1130,f248])).
% 1.46/0.56  fof(f248,plain,(
% 1.46/0.56    v1_funct_1(k1_xboole_0) | ~spl3_13),
% 1.46/0.56    inference(backward_demodulation,[],[f46,f233])).
% 1.46/0.56  fof(f233,plain,(
% 1.46/0.56    k1_xboole_0 = sK2 | ~spl3_13),
% 1.46/0.56    inference(avatar_component_clause,[],[f231])).
% 1.46/0.56  fof(f231,plain,(
% 1.46/0.56    spl3_13 <=> k1_xboole_0 = sK2),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.46/0.56  fof(f46,plain,(
% 1.46/0.56    v1_funct_1(sK2)),
% 1.46/0.56    inference(cnf_transformation,[],[f41])).
% 1.46/0.56  fof(f1130,plain,(
% 1.46/0.56    r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | (~spl3_8 | ~spl3_13)),
% 1.46/0.56    inference(subsumption_resolution,[],[f1122,f1109])).
% 1.46/0.56  fof(f1109,plain,(
% 1.46/0.56    v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) | (~spl3_8 | ~spl3_13)),
% 1.46/0.56    inference(backward_demodulation,[],[f1092,f1108])).
% 1.46/0.56  fof(f1108,plain,(
% 1.46/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0) | (~spl3_8 | ~spl3_13)),
% 1.46/0.56    inference(backward_demodulation,[],[f1090,f147])).
% 1.46/0.56  fof(f1090,plain,(
% 1.46/0.56    k2_struct_0(sK1) = k2_relat_1(k1_xboole_0) | ~spl3_13),
% 1.46/0.56    inference(backward_demodulation,[],[f679,f233])).
% 1.46/0.56  fof(f1092,plain,(
% 1.46/0.56    v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k2_relat_1(k1_xboole_0)) | ~spl3_13),
% 1.46/0.56    inference(forward_demodulation,[],[f695,f233])).
% 1.46/0.56  fof(f695,plain,(
% 1.46/0.56    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 1.46/0.56    inference(backward_demodulation,[],[f126,f679])).
% 1.46/0.56  fof(f1122,plain,(
% 1.46/0.56    r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | (~spl3_8 | ~spl3_13)),
% 1.46/0.56    inference(resolution,[],[f1112,f83])).
% 1.46/0.56  fof(f83,plain,(
% 1.46/0.56    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X3,X3) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.46/0.56    inference(duplicate_literal_removal,[],[f82])).
% 1.46/0.56  fof(f82,plain,(
% 1.46/0.56    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.46/0.56    inference(equality_resolution,[],[f76])).
% 1.46/0.56  fof(f76,plain,(
% 1.46/0.56    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f43])).
% 1.46/0.56  fof(f43,plain,(
% 1.46/0.56    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.46/0.56    inference(nnf_transformation,[],[f37])).
% 1.46/0.56  fof(f37,plain,(
% 1.46/0.56    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.46/0.56    inference(flattening,[],[f36])).
% 1.46/0.56  fof(f36,plain,(
% 1.46/0.56    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.46/0.56    inference(ennf_transformation,[],[f8])).
% 1.46/0.56  fof(f8,axiom,(
% 1.46/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 1.46/0.56  fof(f1112,plain,(
% 1.46/0.56    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | (~spl3_8 | ~spl3_13)),
% 1.46/0.56    inference(forward_demodulation,[],[f1111,f1108])).
% 1.46/0.56  fof(f1111,plain,(
% 1.46/0.56    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(k1_xboole_0)))) | ~spl3_13),
% 1.46/0.56    inference(forward_demodulation,[],[f696,f233])).
% 1.46/0.56  fof(f1458,plain,(
% 1.46/0.56    ~r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl3_8 | ~spl3_10 | ~spl3_13 | ~spl3_37)),
% 1.46/0.56    inference(backward_demodulation,[],[f1196,f1419])).
% 1.46/0.56  fof(f1419,plain,(
% 1.46/0.56    k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) | ~spl3_37),
% 1.46/0.56    inference(avatar_component_clause,[],[f1417])).
% 1.46/0.56  fof(f1417,plain,(
% 1.46/0.56    spl3_37 <=> k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 1.46/0.56  fof(f1196,plain,(
% 1.46/0.56    ~r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k1_xboole_0) | (~spl3_8 | ~spl3_10 | ~spl3_13)),
% 1.46/0.56    inference(backward_demodulation,[],[f1136,f1147])).
% 1.46/0.56  fof(f1147,plain,(
% 1.46/0.56    k2_funct_1(k1_xboole_0) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0) | (~spl3_10 | ~spl3_13)),
% 1.46/0.56    inference(forward_demodulation,[],[f201,f233])).
% 1.46/0.56  fof(f201,plain,(
% 1.46/0.56    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,sK2) | ~spl3_10),
% 1.46/0.56    inference(avatar_component_clause,[],[f199])).
% 1.46/0.56  fof(f199,plain,(
% 1.46/0.56    spl3_10 <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,sK2)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.46/0.56  fof(f1136,plain,(
% 1.46/0.56    ~r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0)),k1_xboole_0) | (~spl3_8 | ~spl3_13)),
% 1.46/0.56    inference(forward_demodulation,[],[f1135,f1108])).
% 1.46/0.56  fof(f1135,plain,(
% 1.46/0.56    ~r2_funct_2(k2_struct_0(sK0),k2_relat_1(k1_xboole_0),k2_tops_2(k2_relat_1(k1_xboole_0),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(k1_xboole_0),k1_xboole_0)),k1_xboole_0) | ~spl3_13),
% 1.46/0.56    inference(forward_demodulation,[],[f702,f233])).
% 1.46/0.56  fof(f702,plain,(
% 1.46/0.56    ~r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2)),
% 1.46/0.56    inference(backward_demodulation,[],[f528,f679])).
% 1.46/0.56  fof(f528,plain,(
% 1.46/0.56    ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)),
% 1.46/0.56    inference(forward_demodulation,[],[f527,f84])).
% 1.46/0.56  fof(f527,plain,(
% 1.46/0.56    ~r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)),
% 1.46/0.56    inference(forward_demodulation,[],[f51,f85])).
% 1.46/0.56  fof(f51,plain,(
% 1.46/0.56    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 1.46/0.56    inference(cnf_transformation,[],[f41])).
% 1.46/0.56  fof(f1452,plain,(
% 1.46/0.56    ~spl3_6 | ~spl3_11 | ~spl3_12 | ~spl3_13 | spl3_38),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f1451])).
% 1.46/0.56  fof(f1451,plain,(
% 1.46/0.56    $false | (~spl3_6 | ~spl3_11 | ~spl3_12 | ~spl3_13 | spl3_38)),
% 1.46/0.56    inference(subsumption_resolution,[],[f1450,f255])).
% 1.46/0.56  fof(f255,plain,(
% 1.46/0.56    v1_funct_1(k2_funct_1(k1_xboole_0)) | (~spl3_6 | ~spl3_13)),
% 1.46/0.56    inference(backward_demodulation,[],[f123,f233])).
% 1.46/0.56  fof(f123,plain,(
% 1.46/0.56    v1_funct_1(k2_funct_1(sK2)) | ~spl3_6),
% 1.46/0.56    inference(avatar_component_clause,[],[f121])).
% 1.46/0.56  fof(f121,plain,(
% 1.46/0.56    spl3_6 <=> v1_funct_1(k2_funct_1(sK2))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.46/0.56  fof(f1450,plain,(
% 1.46/0.56    ~v1_funct_1(k2_funct_1(k1_xboole_0)) | (~spl3_11 | ~spl3_12 | ~spl3_13 | spl3_38)),
% 1.46/0.56    inference(subsumption_resolution,[],[f1449,f1146])).
% 1.46/0.56  fof(f1146,plain,(
% 1.46/0.56    v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) | (~spl3_11 | ~spl3_13)),
% 1.46/0.56    inference(forward_demodulation,[],[f209,f233])).
% 1.46/0.56  fof(f209,plain,(
% 1.46/0.56    v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) | ~spl3_11),
% 1.46/0.56    inference(avatar_component_clause,[],[f207])).
% 1.46/0.56  fof(f207,plain,(
% 1.46/0.56    spl3_11 <=> v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.46/0.56  fof(f1449,plain,(
% 1.46/0.56    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(k1_xboole_0)) | (~spl3_12 | ~spl3_13 | spl3_38)),
% 1.46/0.56    inference(subsumption_resolution,[],[f1448,f1145])).
% 1.46/0.56  fof(f1145,plain,(
% 1.46/0.56    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | (~spl3_12 | ~spl3_13)),
% 1.46/0.56    inference(forward_demodulation,[],[f217,f233])).
% 1.46/0.56  fof(f217,plain,(
% 1.46/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | ~spl3_12),
% 1.46/0.56    inference(avatar_component_clause,[],[f215])).
% 1.46/0.56  fof(f215,plain,(
% 1.46/0.56    spl3_12 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.46/0.56  fof(f1448,plain,(
% 1.46/0.56    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(k1_xboole_0)) | spl3_38),
% 1.46/0.56    inference(resolution,[],[f1423,f69])).
% 1.46/0.56  fof(f69,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f31])).
% 1.46/0.56  fof(f31,plain,(
% 1.46/0.56    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.46/0.56    inference(flattening,[],[f30])).
% 1.46/0.56  fof(f30,plain,(
% 1.46/0.56    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.46/0.56    inference(ennf_transformation,[],[f12])).
% 1.46/0.56  fof(f12,axiom,(
% 1.46/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).
% 1.46/0.56  fof(f1423,plain,(
% 1.46/0.56    ~v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) | spl3_38),
% 1.46/0.56    inference(avatar_component_clause,[],[f1421])).
% 1.46/0.56  fof(f1421,plain,(
% 1.46/0.56    spl3_38 <=> v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 1.46/0.56  fof(f1424,plain,(
% 1.46/0.56    spl3_37 | ~spl3_38 | ~spl3_6 | ~spl3_11 | ~spl3_12 | ~spl3_13 | spl3_14),
% 1.46/0.56    inference(avatar_split_clause,[],[f1415,f235,f231,f215,f207,f121,f1421,f1417])).
% 1.46/0.56  fof(f1415,plain,(
% 1.46/0.56    ~v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) | k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) | (~spl3_6 | ~spl3_11 | ~spl3_12 | ~spl3_13 | spl3_14)),
% 1.46/0.56    inference(subsumption_resolution,[],[f1406,f236])).
% 1.46/0.56  fof(f236,plain,(
% 1.46/0.56    k1_xboole_0 != k2_struct_0(sK0) | spl3_14),
% 1.46/0.56    inference(avatar_component_clause,[],[f235])).
% 1.46/0.56  fof(f1406,plain,(
% 1.46/0.56    ~v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) | k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) | (~spl3_6 | ~spl3_11 | ~spl3_12 | ~spl3_13)),
% 1.46/0.56    inference(resolution,[],[f1190,f79])).
% 1.46/0.56  fof(f79,plain,(
% 1.46/0.56    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2) )),
% 1.46/0.56    inference(equality_resolution,[],[f66])).
% 1.46/0.56  fof(f66,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.46/0.56    inference(cnf_transformation,[],[f42])).
% 1.46/0.56  fof(f1190,plain,(
% 1.46/0.56    m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | (~spl3_6 | ~spl3_11 | ~spl3_12 | ~spl3_13)),
% 1.46/0.56    inference(subsumption_resolution,[],[f1189,f255])).
% 1.46/0.56  fof(f1189,plain,(
% 1.46/0.56    m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_1(k2_funct_1(k1_xboole_0)) | (~spl3_11 | ~spl3_12 | ~spl3_13)),
% 1.46/0.56    inference(subsumption_resolution,[],[f1179,f1146])).
% 1.46/0.56  fof(f1179,plain,(
% 1.46/0.56    m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(k1_xboole_0)) | (~spl3_12 | ~spl3_13)),
% 1.46/0.56    inference(resolution,[],[f1145,f70])).
% 1.46/0.56  fof(f70,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f31])).
% 1.46/0.56  fof(f1144,plain,(
% 1.46/0.56    ~spl3_8 | spl3_9 | ~spl3_13),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f1143])).
% 1.46/0.56  fof(f1143,plain,(
% 1.46/0.56    $false | (~spl3_8 | spl3_9 | ~spl3_13)),
% 1.46/0.56    inference(subsumption_resolution,[],[f1142,f1112])).
% 1.46/0.56  fof(f1142,plain,(
% 1.46/0.56    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | (spl3_9 | ~spl3_13)),
% 1.46/0.56    inference(forward_demodulation,[],[f197,f233])).
% 1.46/0.56  fof(f197,plain,(
% 1.46/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | spl3_9),
% 1.46/0.56    inference(avatar_component_clause,[],[f195])).
% 1.46/0.56  fof(f195,plain,(
% 1.46/0.56    spl3_9 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.46/0.56  fof(f1056,plain,(
% 1.46/0.56    ~spl3_3 | ~spl3_4 | ~spl3_6 | ~spl3_7 | ~spl3_26),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f1055])).
% 1.46/0.56  fof(f1055,plain,(
% 1.46/0.56    $false | (~spl3_3 | ~spl3_4 | ~spl3_6 | ~spl3_7 | ~spl3_26)),
% 1.46/0.56    inference(subsumption_resolution,[],[f1052,f936])).
% 1.46/0.56  fof(f936,plain,(
% 1.46/0.56    r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | ~spl3_7),
% 1.46/0.56    inference(backward_demodulation,[],[f700,f928])).
% 1.46/0.56  fof(f928,plain,(
% 1.46/0.56    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_7),
% 1.46/0.56    inference(forward_demodulation,[],[f722,f697])).
% 1.46/0.56  fof(f697,plain,(
% 1.46/0.56    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 1.46/0.56    inference(backward_demodulation,[],[f130,f679])).
% 1.46/0.56  fof(f130,plain,(
% 1.46/0.56    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.46/0.56    inference(resolution,[],[f128,f60])).
% 1.46/0.56  fof(f60,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f26])).
% 1.46/0.56  fof(f26,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.56    inference(ennf_transformation,[],[f5])).
% 1.46/0.56  fof(f5,axiom,(
% 1.46/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.46/0.56  fof(f722,plain,(
% 1.46/0.56    k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~spl3_7),
% 1.46/0.56    inference(forward_demodulation,[],[f143,f679])).
% 1.46/0.56  fof(f143,plain,(
% 1.46/0.56    k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_7),
% 1.46/0.56    inference(avatar_component_clause,[],[f141])).
% 1.46/0.56  fof(f700,plain,(
% 1.46/0.56    r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2)),
% 1.46/0.56    inference(backward_demodulation,[],[f156,f679])).
% 1.46/0.56  fof(f156,plain,(
% 1.46/0.56    r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)),
% 1.46/0.56    inference(subsumption_resolution,[],[f155,f46])).
% 1.46/0.56  fof(f155,plain,(
% 1.46/0.56    r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) | ~v1_funct_1(sK2)),
% 1.46/0.56    inference(subsumption_resolution,[],[f136,f126])).
% 1.46/0.56  fof(f136,plain,(
% 1.46/0.56    r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.46/0.56    inference(resolution,[],[f128,f83])).
% 1.46/0.56  fof(f1052,plain,(
% 1.46/0.56    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | (~spl3_3 | ~spl3_4 | ~spl3_6 | ~spl3_7 | ~spl3_26)),
% 1.46/0.56    inference(backward_demodulation,[],[f985,f1036])).
% 1.46/0.56  fof(f1036,plain,(
% 1.46/0.56    sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_6 | ~spl3_7 | ~spl3_26)),
% 1.46/0.56    inference(forward_demodulation,[],[f1035,f111])).
% 1.46/0.56  fof(f111,plain,(
% 1.46/0.56    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~spl3_4),
% 1.46/0.56    inference(avatar_component_clause,[],[f109])).
% 1.46/0.56  fof(f109,plain,(
% 1.46/0.56    spl3_4 <=> sK2 = k2_funct_1(k2_funct_1(sK2))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.46/0.56  fof(f1035,plain,(
% 1.46/0.56    k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_3 | ~spl3_6 | ~spl3_7 | ~spl3_26)),
% 1.46/0.56    inference(subsumption_resolution,[],[f1034,f123])).
% 1.46/0.56  fof(f1034,plain,(
% 1.46/0.56    k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | (~spl3_3 | ~spl3_7 | ~spl3_26)),
% 1.46/0.56    inference(subsumption_resolution,[],[f1033,f937])).
% 1.46/0.56  fof(f937,plain,(
% 1.46/0.56    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~spl3_7),
% 1.46/0.56    inference(backward_demodulation,[],[f701,f928])).
% 1.46/0.56  fof(f701,plain,(
% 1.46/0.56    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))),
% 1.46/0.56    inference(backward_demodulation,[],[f174,f679])).
% 1.46/0.56  fof(f174,plain,(
% 1.46/0.56    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))),
% 1.46/0.56    inference(subsumption_resolution,[],[f173,f46])).
% 1.46/0.56  fof(f173,plain,(
% 1.46/0.56    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~v1_funct_1(sK2)),
% 1.46/0.56    inference(subsumption_resolution,[],[f172,f126])).
% 1.46/0.56  fof(f172,plain,(
% 1.46/0.56    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.46/0.56    inference(subsumption_resolution,[],[f171,f128])).
% 1.46/0.56  fof(f171,plain,(
% 1.46/0.56    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.46/0.56    inference(subsumption_resolution,[],[f164,f50])).
% 1.46/0.56  fof(f50,plain,(
% 1.46/0.56    v2_funct_1(sK2)),
% 1.46/0.56    inference(cnf_transformation,[],[f41])).
% 1.46/0.56  fof(f164,plain,(
% 1.46/0.56    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.46/0.56    inference(trivial_inequality_removal,[],[f161])).
% 1.46/0.56  fof(f161,plain,(
% 1.46/0.56    k2_struct_0(sK1) != k2_struct_0(sK1) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.46/0.56    inference(superposition,[],[f72,f158])).
% 1.46/0.56  fof(f72,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | v1_funct_2(k2_funct_1(X2),X1,X0) | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f33])).
% 1.46/0.56  fof(f33,plain,(
% 1.46/0.56    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.46/0.56    inference(flattening,[],[f32])).
% 1.46/0.56  fof(f32,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.46/0.56    inference(ennf_transformation,[],[f9])).
% 1.46/0.56  fof(f9,axiom,(
% 1.46/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 1.46/0.56  fof(f1033,plain,(
% 1.46/0.56    k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | (~spl3_3 | ~spl3_7 | ~spl3_26)),
% 1.46/0.56    inference(subsumption_resolution,[],[f1032,f955])).
% 1.46/0.56  fof(f955,plain,(
% 1.46/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~spl3_7),
% 1.46/0.56    inference(forward_demodulation,[],[f724,f928])).
% 1.46/0.56  fof(f724,plain,(
% 1.46/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))),
% 1.46/0.56    inference(forward_demodulation,[],[f178,f679])).
% 1.46/0.56  fof(f178,plain,(
% 1.46/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 1.46/0.56    inference(subsumption_resolution,[],[f177,f46])).
% 1.46/0.56  fof(f177,plain,(
% 1.46/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | ~v1_funct_1(sK2)),
% 1.46/0.56    inference(subsumption_resolution,[],[f176,f126])).
% 1.46/0.56  fof(f176,plain,(
% 1.46/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.46/0.56    inference(subsumption_resolution,[],[f175,f128])).
% 1.46/0.56  fof(f175,plain,(
% 1.46/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.46/0.56    inference(subsumption_resolution,[],[f163,f50])).
% 1.46/0.56  fof(f163,plain,(
% 1.46/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.46/0.56    inference(trivial_inequality_removal,[],[f162])).
% 1.46/0.56  fof(f162,plain,(
% 1.46/0.56    k2_struct_0(sK1) != k2_struct_0(sK1) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.46/0.56    inference(superposition,[],[f73,f158])).
% 1.46/0.56  fof(f73,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f33])).
% 1.46/0.56  fof(f1032,plain,(
% 1.46/0.56    k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | (~spl3_3 | ~spl3_7 | ~spl3_26)),
% 1.46/0.56    inference(subsumption_resolution,[],[f1031,f567])).
% 1.46/0.56  fof(f567,plain,(
% 1.46/0.56    v2_funct_1(k2_funct_1(sK2)) | ~spl3_26),
% 1.46/0.56    inference(avatar_component_clause,[],[f566])).
% 1.46/0.56  fof(f566,plain,(
% 1.46/0.56    spl3_26 <=> v2_funct_1(k2_funct_1(sK2))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 1.46/0.56  fof(f1031,plain,(
% 1.46/0.56    ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | (~spl3_3 | ~spl3_7)),
% 1.46/0.56    inference(trivial_inequality_removal,[],[f1024])).
% 1.46/0.56  fof(f1024,plain,(
% 1.46/0.56    k1_relat_1(sK2) != k1_relat_1(sK2) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | (~spl3_3 | ~spl3_7)),
% 1.46/0.56    inference(superposition,[],[f74,f997])).
% 1.46/0.56  fof(f997,plain,(
% 1.46/0.56    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_3 | ~spl3_7)),
% 1.46/0.56    inference(forward_demodulation,[],[f990,f105])).
% 1.46/0.56  fof(f105,plain,(
% 1.46/0.56    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_3),
% 1.46/0.56    inference(avatar_component_clause,[],[f103])).
% 1.46/0.56  fof(f103,plain,(
% 1.46/0.56    spl3_3 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.46/0.56  fof(f990,plain,(
% 1.46/0.56    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_7),
% 1.46/0.56    inference(resolution,[],[f955,f61])).
% 1.46/0.56  fof(f74,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f35])).
% 1.46/0.56  fof(f35,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.46/0.56    inference(flattening,[],[f34])).
% 1.46/0.56  fof(f34,plain,(
% 1.46/0.56    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.46/0.56    inference(ennf_transformation,[],[f11])).
% 1.46/0.56  fof(f11,axiom,(
% 1.46/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 1.46/0.56  fof(f985,plain,(
% 1.46/0.56    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2) | ~spl3_7),
% 1.46/0.56    inference(backward_demodulation,[],[f938,f954])).
% 1.46/0.56  fof(f954,plain,(
% 1.46/0.56    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_7),
% 1.46/0.56    inference(forward_demodulation,[],[f723,f928])).
% 1.46/0.56  fof(f723,plain,(
% 1.46/0.56    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 1.46/0.56    inference(forward_demodulation,[],[f170,f679])).
% 1.46/0.56  fof(f170,plain,(
% 1.46/0.56    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.46/0.56    inference(subsumption_resolution,[],[f169,f46])).
% 1.46/0.56  fof(f169,plain,(
% 1.46/0.56    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v1_funct_1(sK2)),
% 1.46/0.56    inference(subsumption_resolution,[],[f168,f126])).
% 1.46/0.56  fof(f168,plain,(
% 1.46/0.56    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.46/0.56    inference(subsumption_resolution,[],[f167,f128])).
% 1.46/0.56  fof(f167,plain,(
% 1.46/0.56    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.46/0.56    inference(subsumption_resolution,[],[f166,f50])).
% 1.46/0.56  fof(f166,plain,(
% 1.46/0.56    ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.46/0.56    inference(trivial_inequality_removal,[],[f159])).
% 1.46/0.56  fof(f159,plain,(
% 1.46/0.56    k2_struct_0(sK1) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.46/0.56    inference(superposition,[],[f74,f158])).
% 1.46/0.56  fof(f938,plain,(
% 1.46/0.56    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2) | ~spl3_7),
% 1.46/0.56    inference(backward_demodulation,[],[f702,f928])).
% 1.46/0.56  fof(f601,plain,(
% 1.46/0.56    ~spl3_1 | spl3_26),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f600])).
% 1.46/0.56  fof(f600,plain,(
% 1.46/0.56    $false | (~spl3_1 | spl3_26)),
% 1.46/0.56    inference(subsumption_resolution,[],[f599,f94])).
% 1.46/0.56  fof(f94,plain,(
% 1.46/0.56    v1_relat_1(sK2) | ~spl3_1),
% 1.46/0.56    inference(avatar_component_clause,[],[f93])).
% 1.46/0.56  fof(f93,plain,(
% 1.46/0.56    spl3_1 <=> v1_relat_1(sK2)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.46/0.56  fof(f599,plain,(
% 1.46/0.56    ~v1_relat_1(sK2) | spl3_26),
% 1.46/0.56    inference(subsumption_resolution,[],[f598,f46])).
% 1.46/0.56  fof(f598,plain,(
% 1.46/0.56    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_26),
% 1.46/0.56    inference(subsumption_resolution,[],[f597,f50])).
% 1.46/0.56  fof(f597,plain,(
% 1.46/0.56    ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_26),
% 1.46/0.56    inference(resolution,[],[f568,f55])).
% 1.46/0.56  fof(f55,plain,(
% 1.46/0.56    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f20])).
% 1.46/0.56  fof(f20,plain,(
% 1.46/0.56    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.46/0.56    inference(flattening,[],[f19])).
% 1.46/0.56  fof(f19,plain,(
% 1.46/0.56    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.46/0.56    inference(ennf_transformation,[],[f1])).
% 1.46/0.56  fof(f1,axiom,(
% 1.46/0.56    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).
% 1.46/0.56  fof(f568,plain,(
% 1.46/0.56    ~v2_funct_1(k2_funct_1(sK2)) | spl3_26),
% 1.46/0.56    inference(avatar_component_clause,[],[f566])).
% 1.46/0.56  fof(f334,plain,(
% 1.46/0.56    ~spl3_9 | spl3_12 | ~spl3_8),
% 1.46/0.56    inference(avatar_split_clause,[],[f333,f145,f215,f195])).
% 1.46/0.56  fof(f333,plain,(
% 1.46/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~spl3_8),
% 1.46/0.56    inference(subsumption_resolution,[],[f332,f46])).
% 1.46/0.56  fof(f332,plain,(
% 1.46/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_1(sK2) | ~spl3_8),
% 1.46/0.56    inference(subsumption_resolution,[],[f331,f181])).
% 1.46/0.56  fof(f331,plain,(
% 1.46/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(sK2) | ~spl3_8),
% 1.46/0.56    inference(subsumption_resolution,[],[f319,f50])).
% 1.46/0.56  fof(f319,plain,(
% 1.46/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(sK2) | ~spl3_8),
% 1.46/0.56    inference(trivial_inequality_removal,[],[f318])).
% 1.46/0.56  fof(f318,plain,(
% 1.46/0.56    k1_xboole_0 != k1_xboole_0 | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(sK2) | ~spl3_8),
% 1.46/0.56    inference(superposition,[],[f73,f179])).
% 1.46/0.56  fof(f179,plain,(
% 1.46/0.56    k1_xboole_0 = k2_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2) | ~spl3_8),
% 1.46/0.56    inference(backward_demodulation,[],[f158,f147])).
% 1.46/0.56  fof(f330,plain,(
% 1.46/0.56    ~spl3_9 | spl3_11 | ~spl3_8),
% 1.46/0.56    inference(avatar_split_clause,[],[f329,f145,f207,f195])).
% 1.46/0.56  fof(f329,plain,(
% 1.46/0.56    v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~spl3_8),
% 1.46/0.56    inference(subsumption_resolution,[],[f328,f46])).
% 1.46/0.56  fof(f328,plain,(
% 1.46/0.56    v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_1(sK2) | ~spl3_8),
% 1.46/0.56    inference(subsumption_resolution,[],[f327,f181])).
% 1.46/0.56  fof(f327,plain,(
% 1.46/0.56    v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(sK2) | ~spl3_8),
% 1.46/0.56    inference(subsumption_resolution,[],[f320,f50])).
% 1.46/0.56  fof(f320,plain,(
% 1.46/0.56    v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(sK2) | ~spl3_8),
% 1.46/0.56    inference(trivial_inequality_removal,[],[f317])).
% 1.46/0.56  fof(f317,plain,(
% 1.46/0.56    k1_xboole_0 != k1_xboole_0 | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(sK2) | ~spl3_8),
% 1.46/0.56    inference(superposition,[],[f72,f179])).
% 1.46/0.56  fof(f326,plain,(
% 1.46/0.56    ~spl3_9 | spl3_10 | ~spl3_8),
% 1.46/0.56    inference(avatar_split_clause,[],[f325,f145,f199,f195])).
% 1.46/0.56  fof(f325,plain,(
% 1.46/0.56    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~spl3_8),
% 1.46/0.56    inference(subsumption_resolution,[],[f324,f46])).
% 1.46/0.56  fof(f324,plain,(
% 1.46/0.56    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_1(sK2) | ~spl3_8),
% 1.46/0.56    inference(subsumption_resolution,[],[f323,f181])).
% 1.46/0.56  fof(f323,plain,(
% 1.46/0.56    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(sK2) | ~spl3_8),
% 1.46/0.56    inference(subsumption_resolution,[],[f322,f50])).
% 1.46/0.56  fof(f322,plain,(
% 1.46/0.56    ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(sK2) | ~spl3_8),
% 1.46/0.56    inference(trivial_inequality_removal,[],[f315])).
% 1.46/0.56  fof(f315,plain,(
% 1.46/0.56    k1_xboole_0 != k1_xboole_0 | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(sK2) | ~spl3_8),
% 1.46/0.56    inference(superposition,[],[f74,f179])).
% 1.46/0.56  fof(f238,plain,(
% 1.46/0.56    spl3_13 | spl3_14 | ~spl3_8),
% 1.46/0.56    inference(avatar_split_clause,[],[f229,f145,f235,f231])).
% 1.46/0.56  fof(f229,plain,(
% 1.46/0.56    k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 = sK2 | ~spl3_8),
% 1.46/0.56    inference(subsumption_resolution,[],[f220,f181])).
% 1.46/0.56  fof(f220,plain,(
% 1.46/0.56    ~v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) | k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 = sK2 | ~spl3_8),
% 1.46/0.56    inference(resolution,[],[f180,f79])).
% 1.46/0.56  fof(f180,plain,(
% 1.46/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~spl3_8),
% 1.46/0.56    inference(backward_demodulation,[],[f128,f147])).
% 1.46/0.56  fof(f148,plain,(
% 1.46/0.56    spl3_7 | spl3_8),
% 1.46/0.56    inference(avatar_split_clause,[],[f139,f145,f141])).
% 1.46/0.56  fof(f139,plain,(
% 1.46/0.56    k1_xboole_0 = k2_struct_0(sK1) | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.46/0.56    inference(subsumption_resolution,[],[f132,f126])).
% 1.46/0.56  fof(f132,plain,(
% 1.46/0.56    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k1_xboole_0 = k2_struct_0(sK1) | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.46/0.56    inference(resolution,[],[f128,f62])).
% 1.46/0.56  fof(f62,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.46/0.56    inference(cnf_transformation,[],[f42])).
% 1.46/0.56  fof(f138,plain,(
% 1.46/0.56    spl3_1),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f137])).
% 1.46/0.56  fof(f137,plain,(
% 1.46/0.56    $false | spl3_1),
% 1.46/0.56    inference(subsumption_resolution,[],[f129,f95])).
% 1.46/0.56  fof(f95,plain,(
% 1.46/0.56    ~v1_relat_1(sK2) | spl3_1),
% 1.46/0.56    inference(avatar_component_clause,[],[f93])).
% 1.46/0.56  fof(f129,plain,(
% 1.46/0.56    v1_relat_1(sK2)),
% 1.46/0.56    inference(resolution,[],[f128,f59])).
% 1.46/0.56  fof(f59,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f25])).
% 1.46/0.56  fof(f25,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.56    inference(ennf_transformation,[],[f4])).
% 1.46/0.56  fof(f4,axiom,(
% 1.46/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.46/0.56  fof(f124,plain,(
% 1.46/0.56    ~spl3_1 | spl3_6),
% 1.46/0.56    inference(avatar_split_clause,[],[f119,f121,f93])).
% 1.46/0.56  fof(f119,plain,(
% 1.46/0.56    v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.46/0.56    inference(subsumption_resolution,[],[f90,f46])).
% 1.46/0.56  fof(f90,plain,(
% 1.46/0.56    v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.46/0.56    inference(resolution,[],[f50,f54])).
% 1.46/0.56  fof(f54,plain,(
% 1.46/0.56    ( ! [X0] : (~v2_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f20])).
% 1.46/0.56  fof(f112,plain,(
% 1.46/0.56    ~spl3_1 | spl3_4),
% 1.46/0.56    inference(avatar_split_clause,[],[f107,f109,f93])).
% 1.46/0.56  fof(f107,plain,(
% 1.46/0.56    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.46/0.56    inference(subsumption_resolution,[],[f88,f46])).
% 1.46/0.56  fof(f88,plain,(
% 1.46/0.56    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.46/0.56    inference(resolution,[],[f50,f56])).
% 1.46/0.56  fof(f56,plain,(
% 1.46/0.56    ( ! [X0] : (~v2_funct_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f22])).
% 1.46/0.56  fof(f22,plain,(
% 1.46/0.56    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.46/0.56    inference(flattening,[],[f21])).
% 1.46/0.56  fof(f21,plain,(
% 1.46/0.56    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.46/0.56    inference(ennf_transformation,[],[f3])).
% 1.46/0.56  fof(f3,axiom,(
% 1.46/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 1.46/0.56  fof(f106,plain,(
% 1.46/0.56    ~spl3_1 | spl3_3),
% 1.46/0.56    inference(avatar_split_clause,[],[f101,f103,f93])).
% 1.46/0.56  fof(f101,plain,(
% 1.46/0.56    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.46/0.56    inference(subsumption_resolution,[],[f87,f46])).
% 1.46/0.56  fof(f87,plain,(
% 1.46/0.56    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.46/0.56    inference(resolution,[],[f50,f58])).
% 1.46/0.56  fof(f58,plain,(
% 1.46/0.56    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f24])).
% 1.46/0.56  fof(f24,plain,(
% 1.46/0.56    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.46/0.56    inference(flattening,[],[f23])).
% 1.46/0.56  fof(f23,plain,(
% 1.46/0.56    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.46/0.56    inference(ennf_transformation,[],[f2])).
% 1.46/0.56  fof(f2,axiom,(
% 1.46/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 1.46/0.56  % SZS output end Proof for theBenchmark
% 1.46/0.56  % (11402)------------------------------
% 1.46/0.56  % (11402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.56  % (11402)Termination reason: Refutation
% 1.46/0.56  
% 1.46/0.56  % (11402)Memory used [KB]: 11129
% 1.46/0.56  % (11402)Time elapsed: 0.143 s
% 1.46/0.56  % (11402)------------------------------
% 1.46/0.56  % (11402)------------------------------
% 1.46/0.56  % (11400)Success in time 0.195 s
%------------------------------------------------------------------------------
