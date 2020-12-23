%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:30 EST 2020

% Result     : Theorem 2.20s
% Output     : Refutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :  266 (33748 expanded)
%              Number of leaves         :   25 (11777 expanded)
%              Depth                    :   36
%              Number of atoms          : 1303 (429396 expanded)
%              Number of equality atoms :  144 (35028 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3287,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3286,f92])).

fof(f92,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f3286,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK5)))))) ),
    inference(subsumption_resolution,[],[f3280,f2772])).

fof(f2772,plain,(
    k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f2116,f2765])).

fof(f2765,plain,(
    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(subsumption_resolution,[],[f2757,f2569])).

fof(f2569,plain,(
    ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1796,f1863])).

fof(f1863,plain,(
    k1_xboole_0 = sK6 ),
    inference(subsumption_resolution,[],[f1862,f92])).

fof(f1862,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK6))
    | k1_xboole_0 = sK6 ),
    inference(forward_demodulation,[],[f1861,f137])).

fof(f137,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1861,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK4),k1_xboole_0),k1_zfmisc_1(sK6))
    | k1_xboole_0 = sK6 ),
    inference(forward_demodulation,[],[f1860,f1714])).

fof(f1714,plain,(
    k1_xboole_0 = u1_struct_0(sK5) ),
    inference(subsumption_resolution,[],[f1708,f1608])).

fof(f1608,plain,
    ( v1_funct_2(sK6,k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | k1_xboole_0 = u1_struct_0(sK5) ),
    inference(resolution,[],[f1603,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X1,X0)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(X2,X1,X0)
        & v1_funct_1(X2) )
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f77])).

fof(f77,plain,(
    ! [X1,X0,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ sP3(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X1,X0,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ sP3(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f1603,plain,
    ( sP3(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),k1_relat_1(sK6),sK6)
    | k1_xboole_0 = u1_struct_0(sK5) ),
    inference(trivial_inequality_removal,[],[f1602])).

fof(f1602,plain,
    ( k1_relat_1(sK6) != k1_relat_1(sK6)
    | sP3(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),k1_relat_1(sK6),sK6)
    | k1_xboole_0 = u1_struct_0(sK5) ),
    inference(superposition,[],[f1277,f425])).

fof(f425,plain,
    ( u1_struct_0(sK4) = k1_relat_1(sK6)
    | k1_xboole_0 = u1_struct_0(sK5) ),
    inference(resolution,[],[f419,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f419,plain,
    ( sP0(u1_struct_0(sK4),u1_struct_0(sK5))
    | u1_struct_0(sK4) = k1_relat_1(sK6) ),
    inference(subsumption_resolution,[],[f418,f270])).

fof(f270,plain,(
    sP1(u1_struct_0(sK4),sK6,u1_struct_0(sK5)) ),
    inference(resolution,[],[f85,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X2,X1,X0)
        & sP1(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f44,f53,f52,f51])).

fof(f52,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f85,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,
    ( ( ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
      | ~ v5_pre_topc(sK6,sK4,sK5) )
    & ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
      | v5_pre_topc(sK6,sK4,sK5) )
    & sK6 = sK7
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    & v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    & v1_funct_1(sK7)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
    & v1_funct_1(sK6)
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f58,f62,f61,f60,f59])).

fof(f59,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | v5_pre_topc(X2,X0,X1) )
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,sK4,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,sK4,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | ~ v5_pre_topc(X2,sK4,X1) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | v5_pre_topc(X2,sK4,X1) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
                | ~ v5_pre_topc(X2,sK4,sK5) )
              & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
                | v5_pre_topc(X2,sK4,sK5) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
              & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
          & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(sK5))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
              | ~ v5_pre_topc(X2,sK4,sK5) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
              | v5_pre_topc(X2,sK4,sK5) )
            & X2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
        & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(sK5))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
            | ~ v5_pre_topc(sK6,sK4,sK5) )
          & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
            | v5_pre_topc(sK6,sK4,sK5) )
          & sK6 = X3
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
          & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
          & v1_funct_1(X3) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
      & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( ? [X3] :
        ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
          | ~ v5_pre_topc(sK6,sK4,sK5) )
        & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
          | v5_pre_topc(sK6,sK4,sK5) )
        & sK6 = X3
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
        & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
        & v1_funct_1(X3) )
   => ( ( ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
        | ~ v5_pre_topc(sK6,sK4,sK5) )
      & ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
        | v5_pre_topc(sK6,sK4,sK5) )
      & sK6 = sK7
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
      & v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                      & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                      & v1_funct_1(X3) )
                   => ( X2 = X3
                     => ( v5_pre_topc(X2,X0,X1)
                      <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_pre_topc)).

fof(f418,plain,
    ( u1_struct_0(sK4) = k1_relat_1(sK6)
    | sP0(u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ sP1(u1_struct_0(sK4),sK6,u1_struct_0(sK5)) ),
    inference(subsumption_resolution,[],[f414,f84])).

fof(f84,plain,(
    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f63])).

fof(f414,plain,
    ( u1_struct_0(sK4) = k1_relat_1(sK6)
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
    | sP0(u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ sP1(u1_struct_0(sK4),sK6,u1_struct_0(sK5)) ),
    inference(superposition,[],[f268,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f74])).

fof(f74,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f268,plain,(
    k1_relset_1(u1_struct_0(sK4),u1_struct_0(sK5),sK6) = k1_relat_1(sK6) ),
    inference(resolution,[],[f85,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f1277,plain,
    ( u1_struct_0(sK4) != k1_relat_1(sK6)
    | sP3(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),k1_relat_1(sK6),sK6) ),
    inference(inner_rewriting,[],[f1276])).

fof(f1276,plain,
    ( u1_struct_0(sK4) != k1_relat_1(sK6)
    | sP3(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK4),sK6) ),
    inference(subsumption_resolution,[],[f1275,f83])).

fof(f83,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f1275,plain,
    ( u1_struct_0(sK4) != k1_relat_1(sK6)
    | sP3(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK4),sK6)
    | ~ v1_funct_1(sK6) ),
    inference(subsumption_resolution,[],[f1271,f706])).

fof(f706,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) ),
    inference(resolution,[],[f274,f629])).

fof(f629,plain,(
    r1_tarski(k2_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    inference(subsumption_resolution,[],[f628,f267])).

fof(f267,plain,(
    v1_relat_1(sK6) ),
    inference(resolution,[],[f85,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f628,plain,
    ( r1_tarski(k2_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ v1_relat_1(sK6) ),
    inference(resolution,[],[f570,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f570,plain,(
    v5_relat_1(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    inference(resolution,[],[f407,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f407,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) ),
    inference(forward_demodulation,[],[f88,f89])).

fof(f89,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f63])).

fof(f88,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) ),
    inference(cnf_transformation,[],[f63])).

fof(f274,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK6),X0)
      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X0))) ) ),
    inference(resolution,[],[f85,f130])).

fof(f130,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

fof(f1271,plain,
    ( u1_struct_0(sK4) != k1_relat_1(sK6)
    | sP3(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK4),sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_1(sK6) ),
    inference(superposition,[],[f129,f923])).

fof(f923,plain,(
    k1_relat_1(sK6) = k1_relset_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),sK6) ),
    inference(resolution,[],[f706,f114])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( sP3(X1,X0,X2)
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( sP3(X1,X0,X2)
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f48,f55])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( k1_relset_1(X0,X1,X2) = X0
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).

fof(f1708,plain,
    ( ~ v1_funct_2(sK6,k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | k1_xboole_0 = u1_struct_0(sK5) ),
    inference(superposition,[],[f1704,f425])).

fof(f1704,plain,(
    ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    inference(subsumption_resolution,[],[f1703,f1649])).

fof(f1649,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
    inference(subsumption_resolution,[],[f1648,f1361])).

fof(f1361,plain,
    ( ~ v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    inference(subsumption_resolution,[],[f583,f706])).

fof(f583,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    inference(subsumption_resolution,[],[f582,f79])).

fof(f79,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f63])).

fof(f582,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f581,f80])).

fof(f80,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f63])).

fof(f581,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f580,f194])).

fof(f194,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
    inference(subsumption_resolution,[],[f185,f81])).

fof(f81,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f63])).

fof(f185,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v2_pre_topc(sK5) ),
    inference(resolution,[],[f82,f96])).

fof(f96,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f82,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f63])).

fof(f580,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f579,f380])).

fof(f380,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
    inference(resolution,[],[f184,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f184,plain,(
    m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
    inference(resolution,[],[f82,f95])).

fof(f95,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f579,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f578,f83])).

fof(f578,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f560,f313])).

fof(f313,plain,(
    v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    inference(forward_demodulation,[],[f87,f89])).

fof(f87,plain,(
    v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    inference(cnf_transformation,[],[f63])).

fof(f560,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(resolution,[],[f407,f146])).

fof(f146,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f134])).

fof(f134,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_pre_topc)).

fof(f1648,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    inference(subsumption_resolution,[],[f651,f706])).

fof(f651,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    inference(subsumption_resolution,[],[f650,f79])).

fof(f650,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f649,f80])).

fof(f649,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f648,f81])).

fof(f648,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f647,f82])).

fof(f647,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f646,f84])).

fof(f646,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f645,f85])).

fof(f645,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f637,f83])).

fof(f637,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(resolution,[],[f413,f144])).

fof(f144,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f132])).

fof(f132,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                    & ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_pre_topc)).

fof(f413,plain,
    ( v5_pre_topc(sK6,sK4,sK5)
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
    inference(forward_demodulation,[],[f90,f89])).

fof(f90,plain,
    ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f63])).

fof(f1703,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    inference(subsumption_resolution,[],[f1702,f1399])).

fof(f1399,plain,
    ( v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    inference(subsumption_resolution,[],[f589,f706])).

fof(f589,plain,
    ( v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    inference(subsumption_resolution,[],[f588,f79])).

fof(f588,plain,
    ( v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f587,f80])).

fof(f587,plain,
    ( v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f586,f194])).

fof(f586,plain,
    ( v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f585,f380])).

fof(f585,plain,
    ( v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f584,f83])).

fof(f584,plain,
    ( v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f561,f313])).

fof(f561,plain,
    ( v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(resolution,[],[f407,f145])).

fof(f145,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f133])).

fof(f133,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f1702,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    inference(subsumption_resolution,[],[f703,f706])).

fof(f703,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    inference(subsumption_resolution,[],[f702,f79])).

fof(f702,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f701,f80])).

fof(f701,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f700,f81])).

fof(f700,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f699,f82])).

fof(f699,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f698,f84])).

fof(f698,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f697,f85])).

fof(f697,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f689,f83])).

fof(f689,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(resolution,[],[f551,f143])).

fof(f143,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f551,plain,
    ( ~ v5_pre_topc(sK6,sK4,sK5)
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
    inference(forward_demodulation,[],[f91,f89])).

fof(f91,plain,
    ( ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f63])).

fof(f1860,plain,
    ( k1_xboole_0 = sK6
    | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)),k1_zfmisc_1(sK6)) ),
    inference(forward_demodulation,[],[f1783,f137])).

fof(f1783,plain,
    ( sK6 = k2_zfmisc_1(u1_struct_0(sK4),k1_xboole_0)
    | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)),k1_zfmisc_1(sK6)) ),
    inference(backward_demodulation,[],[f1307,f1714])).

fof(f1307,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)),k1_zfmisc_1(sK6))
    | k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)) = sK6 ),
    inference(resolution,[],[f405,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f405,plain,
    ( ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)),sK6)
    | k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)) = sK6 ),
    inference(resolution,[],[f275,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f275,plain,(
    r1_tarski(sK6,k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))) ),
    inference(resolution,[],[f85,f108])).

fof(f1796,plain,(
    ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_xboole_0) ),
    inference(backward_demodulation,[],[f1682,f1714])).

fof(f1682,plain,(
    ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) ),
    inference(subsumption_resolution,[],[f1681,f1601])).

fof(f1601,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
    inference(subsumption_resolution,[],[f1600,f1468])).

fof(f1468,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) ),
    inference(subsumption_resolution,[],[f595,f795])).

fof(f795,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) ),
    inference(resolution,[],[f575,f304])).

fof(f304,plain,(
    r1_tarski(k2_relat_1(sK6),u1_struct_0(sK5)) ),
    inference(subsumption_resolution,[],[f303,f267])).

fof(f303,plain,
    ( r1_tarski(k2_relat_1(sK6),u1_struct_0(sK5))
    | ~ v1_relat_1(sK6) ),
    inference(resolution,[],[f269,f101])).

fof(f269,plain,(
    v5_relat_1(sK6,u1_struct_0(sK5)) ),
    inference(resolution,[],[f85,f115])).

fof(f575,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK6),X0)
      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),X0))) ) ),
    inference(resolution,[],[f407,f130])).

fof(f595,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) ),
    inference(subsumption_resolution,[],[f594,f166])).

fof(f166,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(subsumption_resolution,[],[f157,f79])).

fof(f157,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v2_pre_topc(sK4) ),
    inference(resolution,[],[f80,f96])).

fof(f594,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(subsumption_resolution,[],[f593,f261])).

fof(f261,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(resolution,[],[f156,f103])).

fof(f156,plain,(
    m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    inference(resolution,[],[f80,f95])).

fof(f593,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(subsumption_resolution,[],[f592,f81])).

fof(f592,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(subsumption_resolution,[],[f591,f82])).

fof(f591,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(subsumption_resolution,[],[f590,f83])).

fof(f590,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(subsumption_resolution,[],[f562,f313])).

fof(f562,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(resolution,[],[f407,f144])).

fof(f1600,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) ),
    inference(subsumption_resolution,[],[f644,f795])).

fof(f644,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) ),
    inference(subsumption_resolution,[],[f643,f79])).

fof(f643,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f642,f80])).

fof(f642,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f641,f81])).

fof(f641,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f640,f82])).

fof(f640,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f639,f84])).

fof(f639,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f638,f85])).

fof(f638,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f636,f83])).

fof(f636,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(resolution,[],[f413,f146])).

fof(f1681,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) ),
    inference(subsumption_resolution,[],[f1680,f1537])).

fof(f1537,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) ),
    inference(subsumption_resolution,[],[f601,f795])).

fof(f601,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) ),
    inference(subsumption_resolution,[],[f600,f166])).

fof(f600,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(subsumption_resolution,[],[f599,f261])).

fof(f599,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(subsumption_resolution,[],[f598,f81])).

fof(f598,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(subsumption_resolution,[],[f597,f82])).

fof(f597,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(subsumption_resolution,[],[f596,f83])).

fof(f596,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(subsumption_resolution,[],[f563,f313])).

fof(f563,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(resolution,[],[f407,f143])).

fof(f1680,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) ),
    inference(subsumption_resolution,[],[f696,f795])).

fof(f696,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) ),
    inference(subsumption_resolution,[],[f695,f79])).

fof(f695,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f694,f80])).

fof(f694,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f693,f81])).

fof(f693,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f692,f82])).

fof(f692,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f691,f84])).

fof(f691,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f690,f85])).

fof(f690,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f688,f83])).

fof(f688,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(resolution,[],[f551,f145])).

fof(f2757,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_xboole_0)
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(resolution,[],[f2731,f140])).

fof(f140,plain,(
    ! [X2] :
      ( v1_funct_2(k1_xboole_0,X2,k1_xboole_0)
      | k1_xboole_0 = X2
      | ~ sP2(k1_xboole_0,k1_xboole_0,X2) ) ),
    inference(equality_resolution,[],[f139])).

fof(f139,plain,(
    ! [X2,X1] :
      ( v1_funct_2(k1_xboole_0,X2,X1)
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP2(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X0,X2,X1)
      | k1_xboole_0 != X0
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X0,X2,X1)
          | k1_xboole_0 != X0 )
        & ( k1_xboole_0 = X0
          | ~ v1_funct_2(X0,X2,X1) ) )
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f72])).

fof(f72,plain,(
    ! [X2,X1,X0] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_xboole_0 != X2 )
        & ( k1_xboole_0 = X2
          | ~ v1_funct_2(X2,X0,X1) ) )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f2731,plain,(
    sP2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) ),
    inference(forward_demodulation,[],[f1761,f1863])).

fof(f1761,plain,(
    sP2(sK6,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) ),
    inference(backward_demodulation,[],[f1006,f1714])).

fof(f1006,plain,(
    sP2(sK6,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) ),
    inference(resolution,[],[f795,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f2116,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != k1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f1697,f1863])).

fof(f1697,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != k1_relat_1(sK6) ),
    inference(forward_demodulation,[],[f1696,f1003])).

fof(f1003,plain,(
    k1_relat_1(sK6) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5),sK6) ),
    inference(resolution,[],[f795,f114])).

fof(f1696,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5),sK6) ),
    inference(subsumption_resolution,[],[f1693,f795])).

fof(f1693,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5),sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) ),
    inference(resolution,[],[f1683,f205])).

fof(f205,plain,(
    ! [X4,X3] :
      ( sP3(X3,X4,sK6)
      | k1_relset_1(X4,X3,sK6) != X4
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X4,X3))) ) ),
    inference(resolution,[],[f83,f129])).

fof(f1683,plain,(
    ~ sP3(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK6) ),
    inference(resolution,[],[f1682,f127])).

fof(f3280,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK5)))))) ),
    inference(superposition,[],[f3142,f114])).

fof(f3142,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK5))),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f3141,f142])).

fof(f142,plain,(
    ! [X1] : ~ sP0(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f3141,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK5))),k1_xboole_0)
    | sP0(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK5)))) ),
    inference(subsumption_resolution,[],[f3133,f2773])).

fof(f2773,plain,(
    v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK5)))) ),
    inference(backward_demodulation,[],[f2249,f2765])).

fof(f2249,plain,(
    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK5)))) ),
    inference(forward_demodulation,[],[f1729,f1863])).

fof(f1729,plain,(
    v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK5)))) ),
    inference(backward_demodulation,[],[f313,f1714])).

fof(f3133,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK5))),k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK5))))
    | sP0(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK5)))) ),
    inference(resolution,[],[f3132,f118])).

fof(f3132,plain,(
    sP1(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK5)))) ),
    inference(forward_demodulation,[],[f3131,f2765])).

fof(f3131,plain,(
    sP1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK5)))) ),
    inference(forward_demodulation,[],[f1744,f1863])).

fof(f1744,plain,(
    sP1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK6,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK5)))) ),
    inference(backward_demodulation,[],[f571,f1714])).

fof(f571,plain,(
    sP1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    inference(resolution,[],[f407,f122])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:32:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.50  % (11199)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.50  % (11199)Refutation not found, incomplete strategy% (11199)------------------------------
% 0.22/0.50  % (11199)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (11211)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.51  % (11220)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.51  % (11206)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.51  % (11199)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (11199)Memory used [KB]: 10618
% 0.22/0.51  % (11199)Time elapsed: 0.086 s
% 0.22/0.51  % (11199)------------------------------
% 0.22/0.51  % (11199)------------------------------
% 0.22/0.51  % (11202)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (11209)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.51  % (11210)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.51  % (11204)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (11214)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  % (11200)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (11212)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (11221)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.52  % (11213)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (11224)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.52  % (11203)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.52  % (11218)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.52  % (11201)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.52  % (11207)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.52  % (11205)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.53  % (11215)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.53  % (11223)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.53  % (11217)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.53  % (11212)Refutation not found, incomplete strategy% (11212)------------------------------
% 0.22/0.53  % (11212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (11219)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.53  % (11208)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.53  % (11222)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.54  % (11210)Refutation not found, incomplete strategy% (11210)------------------------------
% 0.22/0.54  % (11210)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (11210)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (11210)Memory used [KB]: 10874
% 0.22/0.54  % (11210)Time elapsed: 0.122 s
% 0.22/0.54  % (11210)------------------------------
% 0.22/0.54  % (11210)------------------------------
% 0.22/0.54  % (11216)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.54  % (11212)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (11212)Memory used [KB]: 6268
% 0.22/0.54  % (11212)Time elapsed: 0.110 s
% 0.22/0.54  % (11212)------------------------------
% 0.22/0.54  % (11212)------------------------------
% 0.22/0.55  % (11205)Refutation not found, incomplete strategy% (11205)------------------------------
% 0.22/0.55  % (11205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (11205)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (11205)Memory used [KB]: 10746
% 0.22/0.55  % (11205)Time elapsed: 0.082 s
% 0.22/0.55  % (11205)------------------------------
% 0.22/0.55  % (11205)------------------------------
% 0.22/0.59  % (11200)Refutation not found, incomplete strategy% (11200)------------------------------
% 0.22/0.59  % (11200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (11200)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (11200)Memory used [KB]: 11513
% 0.22/0.59  % (11200)Time elapsed: 0.157 s
% 0.22/0.59  % (11200)------------------------------
% 0.22/0.59  % (11200)------------------------------
% 2.20/0.68  % (11208)Refutation not found, incomplete strategy% (11208)------------------------------
% 2.20/0.68  % (11208)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.68  % (11208)Termination reason: Refutation not found, incomplete strategy
% 2.20/0.68  
% 2.20/0.68  % (11208)Memory used [KB]: 6268
% 2.20/0.68  % (11208)Time elapsed: 0.250 s
% 2.20/0.68  % (11208)------------------------------
% 2.20/0.68  % (11208)------------------------------
% 2.20/0.69  % (11216)Refutation not found, incomplete strategy% (11216)------------------------------
% 2.20/0.69  % (11216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.69  % (11216)Termination reason: Refutation not found, incomplete strategy
% 2.20/0.69  
% 2.20/0.69  % (11216)Memory used [KB]: 6396
% 2.20/0.69  % (11216)Time elapsed: 0.253 s
% 2.20/0.69  % (11216)------------------------------
% 2.20/0.69  % (11216)------------------------------
% 2.20/0.70  % (11207)Refutation found. Thanks to Tanya!
% 2.20/0.70  % SZS status Theorem for theBenchmark
% 2.20/0.70  % SZS output start Proof for theBenchmark
% 2.20/0.70  fof(f3287,plain,(
% 2.20/0.70    $false),
% 2.20/0.70    inference(subsumption_resolution,[],[f3286,f92])).
% 2.20/0.70  fof(f92,plain,(
% 2.20/0.70    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.20/0.70    inference(cnf_transformation,[],[f3])).
% 2.20/0.70  fof(f3,axiom,(
% 2.20/0.70    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.20/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 2.20/0.70  fof(f3286,plain,(
% 2.20/0.70    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK5))))))),
% 2.20/0.70    inference(subsumption_resolution,[],[f3280,f2772])).
% 2.20/0.70  fof(f2772,plain,(
% 2.20/0.70    k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 2.20/0.70    inference(backward_demodulation,[],[f2116,f2765])).
% 2.20/0.70  fof(f2765,plain,(
% 2.20/0.70    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),
% 2.20/0.70    inference(subsumption_resolution,[],[f2757,f2569])).
% 2.20/0.70  fof(f2569,plain,(
% 2.20/0.70    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_xboole_0)),
% 2.20/0.70    inference(forward_demodulation,[],[f1796,f1863])).
% 2.20/0.70  fof(f1863,plain,(
% 2.20/0.70    k1_xboole_0 = sK6),
% 2.20/0.70    inference(subsumption_resolution,[],[f1862,f92])).
% 2.20/0.70  fof(f1862,plain,(
% 2.20/0.70    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK6)) | k1_xboole_0 = sK6),
% 2.20/0.70    inference(forward_demodulation,[],[f1861,f137])).
% 2.20/0.70  fof(f137,plain,(
% 2.20/0.70    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.20/0.70    inference(equality_resolution,[],[f112])).
% 2.20/0.70  fof(f112,plain,(
% 2.20/0.70    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 2.20/0.70    inference(cnf_transformation,[],[f71])).
% 2.20/0.70  fof(f71,plain,(
% 2.20/0.70    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.20/0.70    inference(flattening,[],[f70])).
% 2.20/0.70  fof(f70,plain,(
% 2.20/0.70    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.20/0.70    inference(nnf_transformation,[],[f2])).
% 2.20/0.70  fof(f2,axiom,(
% 2.20/0.70    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.20/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.20/0.70  fof(f1861,plain,(
% 2.20/0.70    ~m1_subset_1(k2_zfmisc_1(u1_struct_0(sK4),k1_xboole_0),k1_zfmisc_1(sK6)) | k1_xboole_0 = sK6),
% 2.20/0.70    inference(forward_demodulation,[],[f1860,f1714])).
% 2.20/0.70  fof(f1714,plain,(
% 2.20/0.70    k1_xboole_0 = u1_struct_0(sK5)),
% 2.20/0.70    inference(subsumption_resolution,[],[f1708,f1608])).
% 2.20/0.70  fof(f1608,plain,(
% 2.20/0.70    v1_funct_2(sK6,k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | k1_xboole_0 = u1_struct_0(sK5)),
% 2.20/0.70    inference(resolution,[],[f1603,f127])).
% 2.20/0.70  fof(f127,plain,(
% 2.20/0.70    ( ! [X2,X0,X1] : (v1_funct_2(X2,X1,X0) | ~sP3(X0,X1,X2)) )),
% 2.20/0.70    inference(cnf_transformation,[],[f78])).
% 2.20/0.70  fof(f78,plain,(
% 2.20/0.70    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X2,X1,X0) & v1_funct_1(X2)) | ~sP3(X0,X1,X2))),
% 2.20/0.70    inference(rectify,[],[f77])).
% 2.20/0.70  fof(f77,plain,(
% 2.20/0.70    ! [X1,X0,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~sP3(X1,X0,X2))),
% 2.20/0.70    inference(nnf_transformation,[],[f55])).
% 2.20/0.70  fof(f55,plain,(
% 2.20/0.70    ! [X1,X0,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~sP3(X1,X0,X2))),
% 2.20/0.70    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 2.20/0.70  fof(f1603,plain,(
% 2.20/0.70    sP3(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),k1_relat_1(sK6),sK6) | k1_xboole_0 = u1_struct_0(sK5)),
% 2.20/0.70    inference(trivial_inequality_removal,[],[f1602])).
% 2.20/0.70  fof(f1602,plain,(
% 2.20/0.70    k1_relat_1(sK6) != k1_relat_1(sK6) | sP3(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),k1_relat_1(sK6),sK6) | k1_xboole_0 = u1_struct_0(sK5)),
% 2.20/0.70    inference(superposition,[],[f1277,f425])).
% 2.20/0.70  fof(f425,plain,(
% 2.20/0.70    u1_struct_0(sK4) = k1_relat_1(sK6) | k1_xboole_0 = u1_struct_0(sK5)),
% 2.20/0.70    inference(resolution,[],[f419,f120])).
% 2.20/0.70  fof(f120,plain,(
% 2.20/0.70    ( ! [X0,X1] : (k1_xboole_0 = X1 | ~sP0(X0,X1)) )),
% 2.20/0.70    inference(cnf_transformation,[],[f76])).
% 2.20/0.70  fof(f76,plain,(
% 2.20/0.70    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 2.20/0.70    inference(nnf_transformation,[],[f51])).
% 2.20/0.70  fof(f51,plain,(
% 2.20/0.70    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 2.20/0.70    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.20/0.70  fof(f419,plain,(
% 2.20/0.70    sP0(u1_struct_0(sK4),u1_struct_0(sK5)) | u1_struct_0(sK4) = k1_relat_1(sK6)),
% 2.20/0.70    inference(subsumption_resolution,[],[f418,f270])).
% 2.20/0.70  fof(f270,plain,(
% 2.20/0.70    sP1(u1_struct_0(sK4),sK6,u1_struct_0(sK5))),
% 2.20/0.70    inference(resolution,[],[f85,f122])).
% 2.20/0.70  fof(f122,plain,(
% 2.20/0.70    ( ! [X2,X0,X1] : (sP1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.20/0.70    inference(cnf_transformation,[],[f54])).
% 2.20/0.70  fof(f54,plain,(
% 2.20/0.70    ! [X0,X1,X2] : ((sP2(X2,X1,X0) & sP1(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.20/0.70    inference(definition_folding,[],[f44,f53,f52,f51])).
% 2.20/0.70  fof(f52,plain,(
% 2.20/0.70    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 2.20/0.70    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.20/0.70  fof(f53,plain,(
% 2.20/0.70    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 2.20/0.70    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 2.20/0.70  fof(f44,plain,(
% 2.20/0.70    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.20/0.70    inference(flattening,[],[f43])).
% 2.20/0.70  fof(f43,plain,(
% 2.20/0.70    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.20/0.70    inference(ennf_transformation,[],[f12])).
% 2.20/0.70  fof(f12,axiom,(
% 2.20/0.70    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.20/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 2.20/0.70  fof(f85,plain,(
% 2.20/0.70    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))),
% 2.20/0.70    inference(cnf_transformation,[],[f63])).
% 2.20/0.70  fof(f63,plain,(
% 2.20/0.70    ((((~v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,sK5)) & (v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,sK4,sK5)) & sK6 = sK7 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) & v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) & v1_funct_1(sK6)) & l1_pre_topc(sK5) & v2_pre_topc(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4)),
% 2.20/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f58,f62,f61,f60,f59])).
% 2.20/0.70  fof(f59,plain,(
% 2.20/0.70    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK4,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK4,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK4) & v2_pre_topc(sK4))),
% 2.20/0.70    introduced(choice_axiom,[])).
% 2.20/0.70  fof(f60,plain,(
% 2.20/0.70    ? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK4,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK4,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(X2,sK4,sK5)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(X2,sK4,sK5)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(sK5)) & v1_funct_1(X2)) & l1_pre_topc(sK5) & v2_pre_topc(sK5))),
% 2.20/0.70    introduced(choice_axiom,[])).
% 2.20/0.70  fof(f61,plain,(
% 2.20/0.70    ? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(X2,sK4,sK5)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(X2,sK4,sK5)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(sK5)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,sK5)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,sK4,sK5)) & sK6 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) & v1_funct_1(X3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) & v1_funct_1(sK6))),
% 2.20/0.70    introduced(choice_axiom,[])).
% 2.20/0.70  fof(f62,plain,(
% 2.20/0.70    ? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,sK5)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,sK4,sK5)) & sK6 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,sK5)) & (v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,sK4,sK5)) & sK6 = sK7 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) & v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) & v1_funct_1(sK7))),
% 2.20/0.70    introduced(choice_axiom,[])).
% 2.20/0.70  fof(f58,plain,(
% 2.20/0.70    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.20/0.70    inference(flattening,[],[f57])).
% 2.20/0.70  fof(f57,plain,(
% 2.20/0.70    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.20/0.70    inference(nnf_transformation,[],[f28])).
% 2.20/0.70  fof(f28,plain,(
% 2.20/0.70    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.20/0.70    inference(flattening,[],[f27])).
% 2.20/0.70  fof(f27,plain,(
% 2.20/0.70    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.20/0.70    inference(ennf_transformation,[],[f22])).
% 2.20/0.70  fof(f22,negated_conjecture,(
% 2.20/0.70    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 2.20/0.70    inference(negated_conjecture,[],[f21])).
% 2.20/0.70  fof(f21,conjecture,(
% 2.20/0.70    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 2.20/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_pre_topc)).
% 2.20/0.70  fof(f418,plain,(
% 2.20/0.70    u1_struct_0(sK4) = k1_relat_1(sK6) | sP0(u1_struct_0(sK4),u1_struct_0(sK5)) | ~sP1(u1_struct_0(sK4),sK6,u1_struct_0(sK5))),
% 2.20/0.70    inference(subsumption_resolution,[],[f414,f84])).
% 2.20/0.70  fof(f84,plain,(
% 2.20/0.70    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))),
% 2.20/0.70    inference(cnf_transformation,[],[f63])).
% 2.20/0.70  fof(f414,plain,(
% 2.20/0.70    u1_struct_0(sK4) = k1_relat_1(sK6) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) | sP0(u1_struct_0(sK4),u1_struct_0(sK5)) | ~sP1(u1_struct_0(sK4),sK6,u1_struct_0(sK5))),
% 2.20/0.70    inference(superposition,[],[f268,f118])).
% 2.20/0.70  fof(f118,plain,(
% 2.20/0.70    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP0(X0,X2) | ~sP1(X0,X1,X2)) )),
% 2.20/0.70    inference(cnf_transformation,[],[f75])).
% 2.20/0.70  fof(f75,plain,(
% 2.20/0.70    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP0(X0,X2) | ~sP1(X0,X1,X2))),
% 2.20/0.70    inference(rectify,[],[f74])).
% 2.20/0.70  fof(f74,plain,(
% 2.20/0.70    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 2.20/0.70    inference(nnf_transformation,[],[f52])).
% 2.20/0.70  fof(f268,plain,(
% 2.20/0.70    k1_relset_1(u1_struct_0(sK4),u1_struct_0(sK5),sK6) = k1_relat_1(sK6)),
% 2.20/0.70    inference(resolution,[],[f85,f114])).
% 2.20/0.70  fof(f114,plain,(
% 2.20/0.70    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.20/0.70    inference(cnf_transformation,[],[f41])).
% 2.20/0.70  fof(f41,plain,(
% 2.20/0.70    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.20/0.70    inference(ennf_transformation,[],[f9])).
% 2.20/0.70  fof(f9,axiom,(
% 2.20/0.70    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.20/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.20/0.70  fof(f1277,plain,(
% 2.20/0.70    u1_struct_0(sK4) != k1_relat_1(sK6) | sP3(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),k1_relat_1(sK6),sK6)),
% 2.20/0.70    inference(inner_rewriting,[],[f1276])).
% 2.20/0.70  fof(f1276,plain,(
% 2.20/0.70    u1_struct_0(sK4) != k1_relat_1(sK6) | sP3(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK4),sK6)),
% 2.20/0.70    inference(subsumption_resolution,[],[f1275,f83])).
% 2.20/0.70  fof(f83,plain,(
% 2.20/0.70    v1_funct_1(sK6)),
% 2.20/0.70    inference(cnf_transformation,[],[f63])).
% 2.20/0.70  fof(f1275,plain,(
% 2.20/0.70    u1_struct_0(sK4) != k1_relat_1(sK6) | sP3(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK4),sK6) | ~v1_funct_1(sK6)),
% 2.20/0.70    inference(subsumption_resolution,[],[f1271,f706])).
% 2.20/0.70  fof(f706,plain,(
% 2.20/0.70    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))),
% 2.20/0.70    inference(resolution,[],[f274,f629])).
% 2.20/0.70  fof(f629,plain,(
% 2.20/0.70    r1_tarski(k2_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))),
% 2.20/0.70    inference(subsumption_resolution,[],[f628,f267])).
% 2.20/0.70  fof(f267,plain,(
% 2.20/0.70    v1_relat_1(sK6)),
% 2.20/0.70    inference(resolution,[],[f85,f113])).
% 2.20/0.70  fof(f113,plain,(
% 2.20/0.70    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.20/0.70    inference(cnf_transformation,[],[f40])).
% 2.20/0.70  fof(f40,plain,(
% 2.20/0.70    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.20/0.70    inference(ennf_transformation,[],[f7])).
% 2.20/0.70  fof(f7,axiom,(
% 2.20/0.70    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.20/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.20/0.70  fof(f628,plain,(
% 2.20/0.70    r1_tarski(k2_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~v1_relat_1(sK6)),
% 2.20/0.70    inference(resolution,[],[f570,f101])).
% 2.20/0.70  fof(f101,plain,(
% 2.20/0.70    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.20/0.70    inference(cnf_transformation,[],[f66])).
% 2.20/0.70  fof(f66,plain,(
% 2.20/0.70    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.20/0.70    inference(nnf_transformation,[],[f36])).
% 2.20/0.70  fof(f36,plain,(
% 2.20/0.70    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.20/0.70    inference(ennf_transformation,[],[f6])).
% 2.20/0.70  fof(f6,axiom,(
% 2.20/0.70    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.20/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 2.20/0.70  fof(f570,plain,(
% 2.20/0.70    v5_relat_1(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))),
% 2.20/0.70    inference(resolution,[],[f407,f115])).
% 2.20/0.70  fof(f115,plain,(
% 2.20/0.70    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.20/0.70    inference(cnf_transformation,[],[f42])).
% 2.20/0.70  fof(f42,plain,(
% 2.20/0.70    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.20/0.70    inference(ennf_transformation,[],[f25])).
% 2.20/0.70  fof(f25,plain,(
% 2.20/0.70    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.20/0.70    inference(pure_predicate_removal,[],[f8])).
% 2.20/0.70  fof(f8,axiom,(
% 2.20/0.70    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.20/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.20/0.70  fof(f407,plain,(
% 2.20/0.70    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))),
% 2.20/0.70    inference(forward_demodulation,[],[f88,f89])).
% 2.20/0.70  fof(f89,plain,(
% 2.20/0.70    sK6 = sK7),
% 2.20/0.70    inference(cnf_transformation,[],[f63])).
% 2.20/0.70  fof(f88,plain,(
% 2.20/0.70    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))),
% 2.20/0.70    inference(cnf_transformation,[],[f63])).
% 2.20/0.70  fof(f274,plain,(
% 2.20/0.70    ( ! [X0] : (~r1_tarski(k2_relat_1(sK6),X0) | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X0)))) )),
% 2.20/0.70    inference(resolution,[],[f85,f130])).
% 2.20/0.70  fof(f130,plain,(
% 2.20/0.70    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) )),
% 2.20/0.70    inference(cnf_transformation,[],[f50])).
% 2.20/0.70  fof(f50,plain,(
% 2.20/0.70    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 2.20/0.70    inference(flattening,[],[f49])).
% 2.20/0.70  fof(f49,plain,(
% 2.20/0.70    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 2.20/0.70    inference(ennf_transformation,[],[f10])).
% 2.20/0.70  fof(f10,axiom,(
% 2.20/0.70    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 2.20/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).
% 2.20/0.70  fof(f1271,plain,(
% 2.20/0.70    u1_struct_0(sK4) != k1_relat_1(sK6) | sP3(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK4),sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_1(sK6)),
% 2.20/0.70    inference(superposition,[],[f129,f923])).
% 2.20/0.70  fof(f923,plain,(
% 2.20/0.70    k1_relat_1(sK6) = k1_relset_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),sK6)),
% 2.20/0.70    inference(resolution,[],[f706,f114])).
% 2.20/0.70  fof(f129,plain,(
% 2.20/0.70    ( ! [X2,X0,X1] : (sP3(X1,X0,X2) | k1_relset_1(X0,X1,X2) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.20/0.70    inference(cnf_transformation,[],[f56])).
% 2.20/0.70  fof(f56,plain,(
% 2.20/0.70    ! [X0,X1,X2] : (sP3(X1,X0,X2) | k1_relset_1(X0,X1,X2) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.20/0.70    inference(definition_folding,[],[f48,f55])).
% 2.20/0.70  fof(f48,plain,(
% 2.20/0.70    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | k1_relset_1(X0,X1,X2) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.20/0.70    inference(flattening,[],[f47])).
% 2.20/0.70  fof(f47,plain,(
% 2.20/0.70    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | k1_relset_1(X0,X1,X2) != X0) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.20/0.70    inference(ennf_transformation,[],[f14])).
% 2.20/0.70  fof(f14,axiom,(
% 2.20/0.70    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 2.20/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).
% 2.20/0.70  fof(f1708,plain,(
% 2.20/0.70    ~v1_funct_2(sK6,k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | k1_xboole_0 = u1_struct_0(sK5)),
% 2.20/0.70    inference(superposition,[],[f1704,f425])).
% 2.20/0.70  fof(f1704,plain,(
% 2.20/0.70    ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))),
% 2.20/0.70    inference(subsumption_resolution,[],[f1703,f1649])).
% 2.20/0.70  fof(f1649,plain,(
% 2.20/0.70    ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))),
% 2.20/0.70    inference(subsumption_resolution,[],[f1648,f1361])).
% 2.20/0.70  fof(f1361,plain,(
% 2.20/0.70    ~v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))),
% 2.20/0.70    inference(subsumption_resolution,[],[f583,f706])).
% 2.20/0.70  fof(f583,plain,(
% 2.20/0.70    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))),
% 2.20/0.70    inference(subsumption_resolution,[],[f582,f79])).
% 2.20/0.70  fof(f79,plain,(
% 2.20/0.70    v2_pre_topc(sK4)),
% 2.20/0.70    inference(cnf_transformation,[],[f63])).
% 2.20/0.70  fof(f582,plain,(
% 2.20/0.70    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~v2_pre_topc(sK4)),
% 2.20/0.70    inference(subsumption_resolution,[],[f581,f80])).
% 2.20/0.70  fof(f80,plain,(
% 2.20/0.70    l1_pre_topc(sK4)),
% 2.20/0.70    inference(cnf_transformation,[],[f63])).
% 2.20/0.70  fof(f581,plain,(
% 2.20/0.70    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.20/0.70    inference(subsumption_resolution,[],[f580,f194])).
% 2.20/0.70  fof(f194,plain,(
% 2.20/0.70    v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))),
% 2.20/0.70    inference(subsumption_resolution,[],[f185,f81])).
% 2.20/0.70  fof(f81,plain,(
% 2.20/0.70    v2_pre_topc(sK5)),
% 2.20/0.70    inference(cnf_transformation,[],[f63])).
% 2.20/0.70  fof(f185,plain,(
% 2.20/0.70    v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v2_pre_topc(sK5)),
% 2.20/0.70    inference(resolution,[],[f82,f96])).
% 2.20/0.70  fof(f96,plain,(
% 2.20/0.70    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.20/0.70    inference(cnf_transformation,[],[f31])).
% 2.20/0.70  fof(f31,plain,(
% 2.20/0.70    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.20/0.70    inference(flattening,[],[f30])).
% 2.20/0.70  fof(f30,plain,(
% 2.20/0.70    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.20/0.70    inference(ennf_transformation,[],[f23])).
% 2.20/0.70  fof(f23,plain,(
% 2.20/0.70    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 2.20/0.70    inference(pure_predicate_removal,[],[f18])).
% 2.20/0.70  fof(f18,axiom,(
% 2.20/0.70    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 2.20/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).
% 2.20/0.70  fof(f82,plain,(
% 2.20/0.70    l1_pre_topc(sK5)),
% 2.20/0.70    inference(cnf_transformation,[],[f63])).
% 2.20/0.70  fof(f580,plain,(
% 2.20/0.70    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.20/0.70    inference(subsumption_resolution,[],[f579,f380])).
% 2.20/0.70  fof(f380,plain,(
% 2.20/0.70    l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))),
% 2.20/0.70    inference(resolution,[],[f184,f103])).
% 2.20/0.70  fof(f103,plain,(
% 2.20/0.70    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.20/0.70    inference(cnf_transformation,[],[f37])).
% 2.20/0.70  fof(f37,plain,(
% 2.20/0.70    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.20/0.70    inference(ennf_transformation,[],[f24])).
% 2.20/0.70  fof(f24,plain,(
% 2.20/0.70    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 2.20/0.70    inference(pure_predicate_removal,[],[f16])).
% 2.20/0.70  fof(f16,axiom,(
% 2.20/0.70    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 2.20/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 2.20/0.70  fof(f184,plain,(
% 2.20/0.70    m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))),
% 2.20/0.70    inference(resolution,[],[f82,f95])).
% 2.20/0.70  fof(f95,plain,(
% 2.20/0.70    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.20/0.70    inference(cnf_transformation,[],[f29])).
% 2.20/0.70  fof(f29,plain,(
% 2.20/0.70    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.20/0.70    inference(ennf_transformation,[],[f17])).
% 2.20/0.70  fof(f17,axiom,(
% 2.20/0.70    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.20/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 2.20/0.70  fof(f579,plain,(
% 2.20/0.70    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.20/0.70    inference(subsumption_resolution,[],[f578,f83])).
% 2.20/0.70  fof(f578,plain,(
% 2.20/0.70    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v1_funct_1(sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.20/0.70    inference(subsumption_resolution,[],[f560,f313])).
% 2.20/0.70  fof(f313,plain,(
% 2.20/0.70    v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))),
% 2.20/0.70    inference(forward_demodulation,[],[f87,f89])).
% 2.20/0.70  fof(f87,plain,(
% 2.20/0.70    v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))),
% 2.20/0.70    inference(cnf_transformation,[],[f63])).
% 2.20/0.70  fof(f560,plain,(
% 2.20/0.70    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~v1_funct_1(sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.20/0.70    inference(resolution,[],[f407,f146])).
% 2.20/0.70  fof(f146,plain,(
% 2.20/0.70    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.20/0.70    inference(duplicate_literal_removal,[],[f134])).
% 2.20/0.70  fof(f134,plain,(
% 2.20/0.70    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.20/0.70    inference(equality_resolution,[],[f99])).
% 2.20/0.70  fof(f99,plain,(
% 2.20/0.70    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.20/0.70    inference(cnf_transformation,[],[f65])).
% 2.20/0.70  fof(f65,plain,(
% 2.20/0.70    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.20/0.70    inference(nnf_transformation,[],[f35])).
% 2.20/0.70  fof(f35,plain,(
% 2.20/0.70    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.20/0.70    inference(flattening,[],[f34])).
% 2.20/0.70  fof(f34,plain,(
% 2.20/0.70    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.20/0.70    inference(ennf_transformation,[],[f19])).
% 2.20/0.70  fof(f19,axiom,(
% 2.20/0.70    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 2.20/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_pre_topc)).
% 2.20/0.70  fof(f1648,plain,(
% 2.20/0.70    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))),
% 2.20/0.70    inference(subsumption_resolution,[],[f651,f706])).
% 2.20/0.70  fof(f651,plain,(
% 2.20/0.70    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))),
% 2.20/0.70    inference(subsumption_resolution,[],[f650,f79])).
% 2.20/0.70  fof(f650,plain,(
% 2.20/0.70    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~v2_pre_topc(sK4)),
% 2.20/0.70    inference(subsumption_resolution,[],[f649,f80])).
% 2.20/0.70  fof(f649,plain,(
% 2.20/0.70    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.20/0.70    inference(subsumption_resolution,[],[f648,f81])).
% 2.20/0.70  fof(f648,plain,(
% 2.20/0.70    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.20/0.70    inference(subsumption_resolution,[],[f647,f82])).
% 2.20/0.70  fof(f647,plain,(
% 2.20/0.70    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.20/0.70    inference(subsumption_resolution,[],[f646,f84])).
% 2.20/0.70  fof(f646,plain,(
% 2.20/0.70    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.20/0.70    inference(subsumption_resolution,[],[f645,f85])).
% 2.20/0.70  fof(f645,plain,(
% 2.20/0.70    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.20/0.70    inference(subsumption_resolution,[],[f637,f83])).
% 2.20/0.70  fof(f637,plain,(
% 2.20/0.70    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~v1_funct_1(sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.20/0.70    inference(resolution,[],[f413,f144])).
% 2.20/0.70  fof(f144,plain,(
% 2.20/0.70    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.20/0.70    inference(duplicate_literal_removal,[],[f132])).
% 2.20/0.70  fof(f132,plain,(
% 2.20/0.70    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.20/0.70    inference(equality_resolution,[],[f97])).
% 2.20/0.70  fof(f97,plain,(
% 2.20/0.70    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.20/0.70    inference(cnf_transformation,[],[f64])).
% 2.20/0.70  fof(f64,plain,(
% 2.20/0.70    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.20/0.70    inference(nnf_transformation,[],[f33])).
% 2.20/0.70  fof(f33,plain,(
% 2.20/0.70    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.20/0.70    inference(flattening,[],[f32])).
% 2.20/0.70  fof(f32,plain,(
% 2.20/0.70    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.20/0.70    inference(ennf_transformation,[],[f20])).
% 2.20/0.70  fof(f20,axiom,(
% 2.20/0.70    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 2.20/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_pre_topc)).
% 2.20/0.70  fof(f413,plain,(
% 2.20/0.70    v5_pre_topc(sK6,sK4,sK5) | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))),
% 2.20/0.70    inference(forward_demodulation,[],[f90,f89])).
% 2.20/0.70  fof(f90,plain,(
% 2.20/0.70    v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,sK4,sK5)),
% 2.20/0.70    inference(cnf_transformation,[],[f63])).
% 2.20/0.70  fof(f1703,plain,(
% 2.20/0.70    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))),
% 2.20/0.70    inference(subsumption_resolution,[],[f1702,f1399])).
% 2.20/0.70  fof(f1399,plain,(
% 2.20/0.70    v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))),
% 2.20/0.70    inference(subsumption_resolution,[],[f589,f706])).
% 2.20/0.70  fof(f589,plain,(
% 2.20/0.70    v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))),
% 2.20/0.70    inference(subsumption_resolution,[],[f588,f79])).
% 2.20/0.70  fof(f588,plain,(
% 2.20/0.70    v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~v2_pre_topc(sK4)),
% 2.20/0.70    inference(subsumption_resolution,[],[f587,f80])).
% 2.20/0.70  fof(f587,plain,(
% 2.20/0.70    v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.20/0.70    inference(subsumption_resolution,[],[f586,f194])).
% 2.20/0.70  fof(f586,plain,(
% 2.20/0.70    v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.20/0.70    inference(subsumption_resolution,[],[f585,f380])).
% 2.20/0.70  fof(f585,plain,(
% 2.20/0.70    v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.20/0.70    inference(subsumption_resolution,[],[f584,f83])).
% 2.20/0.70  fof(f584,plain,(
% 2.20/0.70    v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v1_funct_1(sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.20/0.70    inference(subsumption_resolution,[],[f561,f313])).
% 2.20/0.70  fof(f561,plain,(
% 2.20/0.70    v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~v1_funct_1(sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.20/0.70    inference(resolution,[],[f407,f145])).
% 2.20/0.70  fof(f145,plain,(
% 2.20/0.70    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.20/0.70    inference(duplicate_literal_removal,[],[f133])).
% 2.20/0.70  fof(f133,plain,(
% 2.20/0.70    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.20/0.70    inference(equality_resolution,[],[f100])).
% 2.20/0.70  fof(f100,plain,(
% 2.20/0.70    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.20/0.70    inference(cnf_transformation,[],[f65])).
% 2.20/0.70  fof(f1702,plain,(
% 2.20/0.70    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))),
% 2.20/0.70    inference(subsumption_resolution,[],[f703,f706])).
% 2.20/0.70  fof(f703,plain,(
% 2.20/0.70    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))),
% 2.20/0.70    inference(subsumption_resolution,[],[f702,f79])).
% 2.20/0.70  fof(f702,plain,(
% 2.20/0.70    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~v2_pre_topc(sK4)),
% 2.20/0.70    inference(subsumption_resolution,[],[f701,f80])).
% 2.20/0.70  fof(f701,plain,(
% 2.20/0.70    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.20/0.70    inference(subsumption_resolution,[],[f700,f81])).
% 2.20/0.70  fof(f700,plain,(
% 2.20/0.70    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.20/0.70    inference(subsumption_resolution,[],[f699,f82])).
% 2.20/0.70  fof(f699,plain,(
% 2.20/0.70    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.20/0.70    inference(subsumption_resolution,[],[f698,f84])).
% 2.20/0.70  fof(f698,plain,(
% 2.20/0.70    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.20/0.70    inference(subsumption_resolution,[],[f697,f85])).
% 2.20/0.70  fof(f697,plain,(
% 2.20/0.70    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.20/0.70    inference(subsumption_resolution,[],[f689,f83])).
% 2.20/0.70  fof(f689,plain,(
% 2.20/0.70    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~v1_funct_1(sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.20/0.70    inference(resolution,[],[f551,f143])).
% 2.20/0.70  fof(f143,plain,(
% 2.20/0.70    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.20/0.70    inference(duplicate_literal_removal,[],[f131])).
% 2.20/0.70  fof(f131,plain,(
% 2.20/0.70    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.20/0.70    inference(equality_resolution,[],[f98])).
% 2.20/0.70  fof(f98,plain,(
% 2.20/0.70    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.20/0.70    inference(cnf_transformation,[],[f64])).
% 2.20/0.70  fof(f551,plain,(
% 2.20/0.70    ~v5_pre_topc(sK6,sK4,sK5) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))),
% 2.20/0.70    inference(forward_demodulation,[],[f91,f89])).
% 2.20/0.70  fof(f91,plain,(
% 2.20/0.70    ~v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,sK5)),
% 2.20/0.70    inference(cnf_transformation,[],[f63])).
% 2.20/0.70  fof(f1860,plain,(
% 2.20/0.70    k1_xboole_0 = sK6 | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)),k1_zfmisc_1(sK6))),
% 2.20/0.70    inference(forward_demodulation,[],[f1783,f137])).
% 2.20/0.70  fof(f1783,plain,(
% 2.20/0.70    sK6 = k2_zfmisc_1(u1_struct_0(sK4),k1_xboole_0) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)),k1_zfmisc_1(sK6))),
% 2.20/0.70    inference(backward_demodulation,[],[f1307,f1714])).
% 2.20/0.70  fof(f1307,plain,(
% 2.20/0.70    ~m1_subset_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)),k1_zfmisc_1(sK6)) | k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)) = sK6),
% 2.20/0.70    inference(resolution,[],[f405,f108])).
% 2.20/0.70  fof(f108,plain,(
% 2.20/0.70    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.20/0.70    inference(cnf_transformation,[],[f69])).
% 2.20/0.70  fof(f69,plain,(
% 2.20/0.70    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.20/0.70    inference(nnf_transformation,[],[f4])).
% 2.20/0.70  fof(f4,axiom,(
% 2.20/0.70    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.20/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.20/0.70  fof(f405,plain,(
% 2.20/0.70    ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)),sK6) | k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)) = sK6),
% 2.20/0.70    inference(resolution,[],[f275,f107])).
% 2.20/0.70  fof(f107,plain,(
% 2.20/0.70    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.20/0.70    inference(cnf_transformation,[],[f68])).
% 2.20/0.70  fof(f68,plain,(
% 2.20/0.70    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.20/0.70    inference(flattening,[],[f67])).
% 2.20/0.70  fof(f67,plain,(
% 2.20/0.70    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.20/0.70    inference(nnf_transformation,[],[f1])).
% 2.20/0.70  fof(f1,axiom,(
% 2.20/0.70    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.20/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.20/0.70  fof(f275,plain,(
% 2.20/0.70    r1_tarski(sK6,k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))),
% 2.20/0.70    inference(resolution,[],[f85,f108])).
% 2.20/0.70  fof(f1796,plain,(
% 2.20/0.70    ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_xboole_0)),
% 2.20/0.70    inference(backward_demodulation,[],[f1682,f1714])).
% 2.20/0.70  fof(f1682,plain,(
% 2.20/0.70    ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))),
% 2.20/0.70    inference(subsumption_resolution,[],[f1681,f1601])).
% 2.20/0.70  fof(f1601,plain,(
% 2.20/0.70    ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))),
% 2.20/0.70    inference(subsumption_resolution,[],[f1600,f1468])).
% 2.20/0.70  fof(f1468,plain,(
% 2.20/0.70    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))),
% 2.20/0.70    inference(subsumption_resolution,[],[f595,f795])).
% 2.20/0.70  fof(f795,plain,(
% 2.20/0.70    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))),
% 2.20/0.70    inference(resolution,[],[f575,f304])).
% 2.20/0.70  fof(f304,plain,(
% 2.20/0.70    r1_tarski(k2_relat_1(sK6),u1_struct_0(sK5))),
% 2.20/0.70    inference(subsumption_resolution,[],[f303,f267])).
% 2.20/0.70  fof(f303,plain,(
% 2.20/0.70    r1_tarski(k2_relat_1(sK6),u1_struct_0(sK5)) | ~v1_relat_1(sK6)),
% 2.20/0.70    inference(resolution,[],[f269,f101])).
% 2.20/0.70  fof(f269,plain,(
% 2.20/0.70    v5_relat_1(sK6,u1_struct_0(sK5))),
% 2.20/0.70    inference(resolution,[],[f85,f115])).
% 2.20/0.70  fof(f575,plain,(
% 2.20/0.70    ( ! [X0] : (~r1_tarski(k2_relat_1(sK6),X0) | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),X0)))) )),
% 2.20/0.70    inference(resolution,[],[f407,f130])).
% 2.20/0.70  fof(f595,plain,(
% 2.20/0.70    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))),
% 2.20/0.70    inference(subsumption_resolution,[],[f594,f166])).
% 2.20/0.70  fof(f166,plain,(
% 2.20/0.70    v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),
% 2.20/0.70    inference(subsumption_resolution,[],[f157,f79])).
% 2.20/0.70  fof(f157,plain,(
% 2.20/0.70    v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v2_pre_topc(sK4)),
% 2.20/0.70    inference(resolution,[],[f80,f96])).
% 2.20/0.70  fof(f594,plain,(
% 2.20/0.70    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),
% 2.20/0.70    inference(subsumption_resolution,[],[f593,f261])).
% 2.20/0.70  fof(f261,plain,(
% 2.20/0.70    l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),
% 2.20/0.70    inference(resolution,[],[f156,f103])).
% 2.20/0.70  fof(f156,plain,(
% 2.20/0.70    m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))),
% 2.20/0.70    inference(resolution,[],[f80,f95])).
% 2.20/0.70  fof(f593,plain,(
% 2.20/0.70    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),
% 2.20/0.70    inference(subsumption_resolution,[],[f592,f81])).
% 2.20/0.70  fof(f592,plain,(
% 2.20/0.70    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~v2_pre_topc(sK5) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),
% 2.20/0.70    inference(subsumption_resolution,[],[f591,f82])).
% 2.20/0.70  fof(f591,plain,(
% 2.20/0.70    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),
% 2.20/0.70    inference(subsumption_resolution,[],[f590,f83])).
% 2.20/0.70  fof(f590,plain,(
% 2.20/0.70    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~v1_funct_1(sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),
% 2.20/0.70    inference(subsumption_resolution,[],[f562,f313])).
% 2.20/0.70  fof(f562,plain,(
% 2.20/0.70    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~v1_funct_1(sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),
% 2.20/0.70    inference(resolution,[],[f407,f144])).
% 2.20/0.70  fof(f1600,plain,(
% 2.20/0.70    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))),
% 2.20/0.70    inference(subsumption_resolution,[],[f644,f795])).
% 2.20/0.70  fof(f644,plain,(
% 2.20/0.70    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))),
% 2.20/0.70    inference(subsumption_resolution,[],[f643,f79])).
% 2.20/0.70  fof(f643,plain,(
% 2.20/0.70    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~v2_pre_topc(sK4)),
% 2.20/0.70    inference(subsumption_resolution,[],[f642,f80])).
% 2.20/0.70  fof(f642,plain,(
% 2.20/0.70    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.20/0.70    inference(subsumption_resolution,[],[f641,f81])).
% 2.20/0.70  fof(f641,plain,(
% 2.20/0.70    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.20/0.70    inference(subsumption_resolution,[],[f640,f82])).
% 2.20/0.70  fof(f640,plain,(
% 2.20/0.70    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.20/0.70    inference(subsumption_resolution,[],[f639,f84])).
% 2.20/0.70  fof(f639,plain,(
% 2.20/0.70    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.20/0.70    inference(subsumption_resolution,[],[f638,f85])).
% 2.20/0.70  fof(f638,plain,(
% 2.20/0.70    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.20/0.70    inference(subsumption_resolution,[],[f636,f83])).
% 2.20/0.70  fof(f636,plain,(
% 2.20/0.70    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~v1_funct_1(sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.20/0.70    inference(resolution,[],[f413,f146])).
% 2.20/0.70  fof(f1681,plain,(
% 2.20/0.70    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))),
% 2.20/0.70    inference(subsumption_resolution,[],[f1680,f1537])).
% 2.20/0.70  fof(f1537,plain,(
% 2.20/0.70    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))),
% 2.20/0.70    inference(subsumption_resolution,[],[f601,f795])).
% 2.20/0.70  fof(f601,plain,(
% 2.20/0.70    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))),
% 2.20/0.70    inference(subsumption_resolution,[],[f600,f166])).
% 2.20/0.70  fof(f600,plain,(
% 2.20/0.70    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),
% 2.20/0.70    inference(subsumption_resolution,[],[f599,f261])).
% 2.20/0.70  fof(f599,plain,(
% 2.20/0.70    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),
% 2.20/0.70    inference(subsumption_resolution,[],[f598,f81])).
% 2.20/0.70  fof(f598,plain,(
% 2.20/0.70    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~v2_pre_topc(sK5) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),
% 2.20/0.70    inference(subsumption_resolution,[],[f597,f82])).
% 2.20/0.70  fof(f597,plain,(
% 2.20/0.70    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),
% 2.20/0.70    inference(subsumption_resolution,[],[f596,f83])).
% 2.20/0.70  fof(f596,plain,(
% 2.20/0.70    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v1_funct_1(sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),
% 2.20/0.70    inference(subsumption_resolution,[],[f563,f313])).
% 2.20/0.70  fof(f563,plain,(
% 2.20/0.70    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~v1_funct_1(sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),
% 2.20/0.70    inference(resolution,[],[f407,f143])).
% 2.20/0.70  fof(f1680,plain,(
% 2.20/0.70    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))),
% 2.20/0.70    inference(subsumption_resolution,[],[f696,f795])).
% 2.20/0.70  fof(f696,plain,(
% 2.20/0.70    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))),
% 2.20/0.70    inference(subsumption_resolution,[],[f695,f79])).
% 2.20/0.70  fof(f695,plain,(
% 2.20/0.70    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~v2_pre_topc(sK4)),
% 2.20/0.70    inference(subsumption_resolution,[],[f694,f80])).
% 2.20/0.70  fof(f694,plain,(
% 2.20/0.70    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.20/0.70    inference(subsumption_resolution,[],[f693,f81])).
% 2.20/0.70  fof(f693,plain,(
% 2.20/0.70    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.20/0.70    inference(subsumption_resolution,[],[f692,f82])).
% 2.20/0.70  fof(f692,plain,(
% 2.20/0.70    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.20/0.70    inference(subsumption_resolution,[],[f691,f84])).
% 2.20/0.70  fof(f691,plain,(
% 2.20/0.70    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.20/0.70    inference(subsumption_resolution,[],[f690,f85])).
% 2.20/0.70  fof(f690,plain,(
% 2.20/0.70    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.20/0.70    inference(subsumption_resolution,[],[f688,f83])).
% 2.20/0.70  fof(f688,plain,(
% 2.20/0.70    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~v1_funct_1(sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.20/0.70    inference(resolution,[],[f551,f145])).
% 2.20/0.70  fof(f2757,plain,(
% 2.20/0.70    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_xboole_0) | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),
% 2.20/0.70    inference(resolution,[],[f2731,f140])).
% 2.20/0.70  fof(f140,plain,(
% 2.20/0.70    ( ! [X2] : (v1_funct_2(k1_xboole_0,X2,k1_xboole_0) | k1_xboole_0 = X2 | ~sP2(k1_xboole_0,k1_xboole_0,X2)) )),
% 2.20/0.70    inference(equality_resolution,[],[f139])).
% 2.20/0.70  fof(f139,plain,(
% 2.20/0.70    ( ! [X2,X1] : (v1_funct_2(k1_xboole_0,X2,X1) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP2(k1_xboole_0,X1,X2)) )),
% 2.20/0.70    inference(equality_resolution,[],[f117])).
% 2.20/0.70  fof(f117,plain,(
% 2.20/0.70    ( ! [X2,X0,X1] : (v1_funct_2(X0,X2,X1) | k1_xboole_0 != X0 | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP2(X0,X1,X2)) )),
% 2.20/0.70    inference(cnf_transformation,[],[f73])).
% 2.20/0.70  fof(f73,plain,(
% 2.20/0.70    ! [X0,X1,X2] : (((v1_funct_2(X0,X2,X1) | k1_xboole_0 != X0) & (k1_xboole_0 = X0 | ~v1_funct_2(X0,X2,X1))) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP2(X0,X1,X2))),
% 2.20/0.70    inference(rectify,[],[f72])).
% 2.20/0.70  fof(f72,plain,(
% 2.20/0.70    ! [X2,X1,X0] : (((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 2.20/0.70    inference(nnf_transformation,[],[f53])).
% 2.20/0.70  fof(f2731,plain,(
% 2.20/0.70    sP2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),
% 2.20/0.70    inference(forward_demodulation,[],[f1761,f1863])).
% 2.20/0.70  fof(f1761,plain,(
% 2.20/0.70    sP2(sK6,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),
% 2.20/0.70    inference(backward_demodulation,[],[f1006,f1714])).
% 2.20/0.70  fof(f1006,plain,(
% 2.20/0.70    sP2(sK6,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),
% 2.20/0.70    inference(resolution,[],[f795,f123])).
% 2.20/0.70  fof(f123,plain,(
% 2.20/0.70    ( ! [X2,X0,X1] : (sP2(X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.20/0.70    inference(cnf_transformation,[],[f54])).
% 2.20/0.70  fof(f2116,plain,(
% 2.20/0.70    u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != k1_relat_1(k1_xboole_0)),
% 2.20/0.70    inference(backward_demodulation,[],[f1697,f1863])).
% 2.20/0.70  fof(f1697,plain,(
% 2.20/0.70    u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != k1_relat_1(sK6)),
% 2.20/0.70    inference(forward_demodulation,[],[f1696,f1003])).
% 2.20/0.70  fof(f1003,plain,(
% 2.20/0.70    k1_relat_1(sK6) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5),sK6)),
% 2.20/0.70    inference(resolution,[],[f795,f114])).
% 2.20/0.70  fof(f1696,plain,(
% 2.20/0.70    u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5),sK6)),
% 2.20/0.70    inference(subsumption_resolution,[],[f1693,f795])).
% 2.20/0.70  fof(f1693,plain,(
% 2.20/0.70    u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5),sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))),
% 2.20/0.70    inference(resolution,[],[f1683,f205])).
% 2.20/0.70  fof(f205,plain,(
% 2.20/0.70    ( ! [X4,X3] : (sP3(X3,X4,sK6) | k1_relset_1(X4,X3,sK6) != X4 | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))) )),
% 2.20/0.70    inference(resolution,[],[f83,f129])).
% 2.20/0.70  fof(f1683,plain,(
% 2.20/0.70    ~sP3(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK6)),
% 2.20/0.70    inference(resolution,[],[f1682,f127])).
% 2.20/0.70  fof(f3280,plain,(
% 2.20/0.70    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK5))))))),
% 2.20/0.70    inference(superposition,[],[f3142,f114])).
% 2.20/0.70  fof(f3142,plain,(
% 2.20/0.70    k1_xboole_0 = k1_relset_1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK5))),k1_xboole_0)),
% 2.20/0.70    inference(subsumption_resolution,[],[f3141,f142])).
% 2.20/0.70  fof(f142,plain,(
% 2.20/0.70    ( ! [X1] : (~sP0(k1_xboole_0,X1)) )),
% 2.20/0.70    inference(equality_resolution,[],[f121])).
% 2.20/0.70  fof(f121,plain,(
% 2.20/0.70    ( ! [X0,X1] : (k1_xboole_0 != X0 | ~sP0(X0,X1)) )),
% 2.20/0.70    inference(cnf_transformation,[],[f76])).
% 2.20/0.70  fof(f3141,plain,(
% 2.20/0.70    k1_xboole_0 = k1_relset_1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK5))),k1_xboole_0) | sP0(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK5))))),
% 2.20/0.70    inference(subsumption_resolution,[],[f3133,f2773])).
% 2.20/0.70  fof(f2773,plain,(
% 2.20/0.70    v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK5))))),
% 2.20/0.70    inference(backward_demodulation,[],[f2249,f2765])).
% 2.20/0.70  fof(f2249,plain,(
% 2.20/0.70    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK5))))),
% 2.20/0.70    inference(forward_demodulation,[],[f1729,f1863])).
% 2.20/0.70  fof(f1729,plain,(
% 2.20/0.70    v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK5))))),
% 2.20/0.70    inference(backward_demodulation,[],[f313,f1714])).
% 2.20/0.70  fof(f3133,plain,(
% 2.20/0.70    k1_xboole_0 = k1_relset_1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK5))),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK5)))) | sP0(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK5))))),
% 2.20/0.70    inference(resolution,[],[f3132,f118])).
% 2.20/0.70  fof(f3132,plain,(
% 2.20/0.70    sP1(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK5))))),
% 2.20/0.70    inference(forward_demodulation,[],[f3131,f2765])).
% 2.20/0.70  fof(f3131,plain,(
% 2.20/0.70    sP1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK5))))),
% 2.20/0.70    inference(forward_demodulation,[],[f1744,f1863])).
% 2.20/0.70  fof(f1744,plain,(
% 2.20/0.70    sP1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK6,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK5))))),
% 2.20/0.70    inference(backward_demodulation,[],[f571,f1714])).
% 2.20/0.70  fof(f571,plain,(
% 2.20/0.70    sP1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))),
% 2.20/0.70    inference(resolution,[],[f407,f122])).
% 2.20/0.70  % SZS output end Proof for theBenchmark
% 2.20/0.70  % (11207)------------------------------
% 2.20/0.70  % (11207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.70  % (11207)Termination reason: Refutation
% 2.20/0.70  
% 2.20/0.70  % (11207)Memory used [KB]: 3326
% 2.20/0.70  % (11207)Time elapsed: 0.292 s
% 2.20/0.70  % (11207)------------------------------
% 2.20/0.70  % (11207)------------------------------
% 2.20/0.70  % (11198)Success in time 0.338 s
%------------------------------------------------------------------------------
