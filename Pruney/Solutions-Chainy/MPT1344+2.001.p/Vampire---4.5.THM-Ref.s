%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:37 EST 2020

% Result     : Theorem 3.68s
% Output     : Refutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :  345 (7184 expanded)
%              Number of leaves         :   39 (2887 expanded)
%              Depth                    :   33
%              Number of atoms          : 1071 (54550 expanded)
%              Number of equality atoms :  304 (15095 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6844,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f230,f403,f759,f858,f859,f881,f941,f1014,f2786,f3293,f3302,f3657,f3857,f5977,f6843])).

fof(f6843,plain,
    ( ~ spl4_3
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_113
    | ~ spl4_135 ),
    inference(avatar_contradiction_clause,[],[f6842])).

fof(f6842,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_113
    | ~ spl4_135 ),
    inference(subsumption_resolution,[],[f6841,f6003])).

fof(f6003,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_113 ),
    inference(superposition,[],[f3963,f5991])).

fof(f5991,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f758,f398])).

fof(f398,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f396])).

fof(f396,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f758,plain,
    ( k1_xboole_0 = k2_funct_1(sK2)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f756])).

fof(f756,plain,
    ( spl4_11
  <=> k1_xboole_0 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f3963,plain,
    ( k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl4_5
    | ~ spl4_113 ),
    inference(forward_demodulation,[],[f3739,f2785])).

fof(f2785,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl4_113 ),
    inference(avatar_component_clause,[],[f2783])).

fof(f2783,plain,
    ( spl4_113
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_113])])).

fof(f3739,plain,
    ( k2_relat_1(k1_xboole_0) = k1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl4_5 ),
    inference(superposition,[],[f127,f398])).

fof(f127,plain,(
    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f126,f115])).

fof(f115,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f83,f62])).

fof(f62,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f51,f50,f49,f48])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X3)
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X3)
                & v2_funct_1(X2)
                & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),X3)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),X3)
            & v2_funct_1(X2)
            & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X3)
          & v2_funct_1(sK2)
          & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X3] :
        ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X3)
        & v2_funct_1(sK2)
        & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)
      & v2_funct_1(sK2)
      & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v2_funct_1(X2)
                        & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                     => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v2_funct_1(X2)
                      & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                   => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_tops_2)).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f126,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f125,f60])).

fof(f60,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f125,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f73,f65])).

fof(f65,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f6841,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_113
    | ~ spl4_135 ),
    inference(forward_demodulation,[],[f6840,f5826])).

fof(f5826,plain,
    ( ! [X10,X9] : k1_xboole_0 = k7_relset_1(X9,X10,k1_xboole_0,X9)
    | ~ spl4_5
    | ~ spl4_113 ),
    inference(forward_demodulation,[],[f5783,f5823])).

fof(f5823,plain,
    ( ! [X4,X3] : k1_xboole_0 = k2_relset_1(X3,X4,k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_113 ),
    inference(forward_demodulation,[],[f5780,f2785])).

fof(f5780,plain,
    ( ! [X4,X3] : k2_relat_1(k1_xboole_0) = k2_relset_1(X3,X4,k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_113 ),
    inference(resolution,[],[f5735,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f5735,plain,
    ( ! [X4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X4))
    | ~ spl4_5
    | ~ spl4_113 ),
    inference(forward_demodulation,[],[f5722,f5731])).

fof(f5731,plain,
    ( ! [X0] : k1_xboole_0 = k1_relset_1(X0,k1_xboole_0,k2_funct_1(k1_xboole_0))
    | ~ spl4_5
    | ~ spl4_113 ),
    inference(forward_demodulation,[],[f5718,f3963])).

fof(f5718,plain,
    ( ! [X0] : k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_relset_1(X0,k1_xboole_0,k2_funct_1(k1_xboole_0))
    | ~ spl4_5
    | ~ spl4_113 ),
    inference(resolution,[],[f3947,f133])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | k1_relset_1(X0,k1_xboole_0,X1) = k1_relat_1(X1) ) ),
    inference(superposition,[],[f84,f101])).

fof(f101,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f3947,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_5
    | ~ spl4_113 ),
    inference(forward_demodulation,[],[f3946,f102])).

fof(f102,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f3946,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
    | ~ spl4_5
    | ~ spl4_113 ),
    inference(forward_demodulation,[],[f3772,f2785])).

fof(f3772,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(k1_xboole_0),k2_struct_0(sK0))))
    | ~ spl4_5 ),
    inference(superposition,[],[f924,f398])).

fof(f924,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f267,f909])).

fof(f909,plain,(
    k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f908,f153])).

fof(f153,plain,(
    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(forward_demodulation,[],[f152,f106])).

fof(f106,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f69,f58])).

fof(f58,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f69,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f152,plain,(
    k2_relat_1(sK2) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(forward_demodulation,[],[f148,f107])).

fof(f107,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f69,f59])).

fof(f59,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f148,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f85,f62])).

fof(f908,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(forward_demodulation,[],[f341,f106])).

fof(f341,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(superposition,[],[f64,f107])).

fof(f64,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f267,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f266,f107])).

fof(f266,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f265,f106])).

fof(f265,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f264,f107])).

fof(f264,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f263,f64])).

fof(f263,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f262,f60])).

fof(f262,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f261,f61])).

fof(f61,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f52])).

fof(f261,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f257,f65])).

fof(f257,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f95,f62])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f5722,plain,
    ( ! [X4] : m1_subset_1(k1_relset_1(X4,k1_xboole_0,k2_funct_1(k1_xboole_0)),k1_zfmisc_1(X4))
    | ~ spl4_5
    | ~ spl4_113 ),
    inference(resolution,[],[f3947,f156])).

fof(f156,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | m1_subset_1(k1_relset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f86,f101])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f5783,plain,
    ( ! [X10,X9] : k2_relset_1(X9,X10,k1_xboole_0) = k7_relset_1(X9,X10,k1_xboole_0,X9)
    | ~ spl4_5
    | ~ spl4_113 ),
    inference(resolution,[],[f5735,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f6840,plain,
    ( k1_relat_1(k1_xboole_0) != k7_relset_1(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_113
    | ~ spl4_135 ),
    inference(superposition,[],[f3957,f5991])).

fof(f3957,plain,
    ( k1_relat_1(k1_xboole_0) != k7_relset_1(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0),k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_113
    | ~ spl4_135 ),
    inference(forward_demodulation,[],[f3956,f3948])).

fof(f3948,plain,
    ( k2_funct_1(k1_xboole_0) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_113 ),
    inference(forward_demodulation,[],[f3771,f2785])).

fof(f3771,plain,
    ( k2_funct_1(k1_xboole_0) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl4_5 ),
    inference(superposition,[],[f923,f398])).

fof(f923,plain,(
    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(forward_demodulation,[],[f922,f106])).

fof(f922,plain,(
    k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(forward_demodulation,[],[f282,f909])).

fof(f282,plain,(
    k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(forward_demodulation,[],[f281,f107])).

fof(f281,plain,(
    k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f280,f107])).

fof(f280,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(forward_demodulation,[],[f279,f64])).

fof(f279,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f278,f60])).

fof(f278,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f277,f61])).

fof(f277,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f273,f65])).

fof(f273,plain,
    ( ~ v2_funct_1(sK2)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f96,f62])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f3956,plain,
    ( k1_relat_1(k1_xboole_0) != k7_relset_1(k1_xboole_0,k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_113
    | ~ spl4_135 ),
    inference(forward_demodulation,[],[f3955,f647])).

fof(f647,plain,(
    ! [X0] : k1_relat_1(k1_xboole_0) = k8_relset_1(X0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f185,f101])).

fof(f185,plain,(
    ! [X0,X1] : k1_relat_1(k2_zfmisc_1(X0,X1)) = k8_relset_1(X0,X1,k2_zfmisc_1(X0,X1),X1) ),
    inference(forward_demodulation,[],[f179,f132])).

fof(f132,plain,(
    ! [X0,X1] : k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1)) = k1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(resolution,[],[f84,f104])).

fof(f104,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f68,f67])).

fof(f67,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f68,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f179,plain,(
    ! [X0,X1] : k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1)) = k8_relset_1(X0,X1,k2_zfmisc_1(X0,X1),X1) ),
    inference(resolution,[],[f89,f104])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f3955,plain,
    ( k7_relset_1(k1_xboole_0,k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0),k1_xboole_0) != k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_113
    | ~ spl4_135 ),
    inference(forward_demodulation,[],[f3853,f2785])).

fof(f3853,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != k7_relset_1(k2_relat_1(k1_xboole_0),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(k1_xboole_0),k1_xboole_0),k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_135 ),
    inference(forward_demodulation,[],[f3768,f3658])).

fof(f3658,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_3
    | ~ spl4_135 ),
    inference(forward_demodulation,[],[f3301,f3308])).

fof(f3308,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl4_3 ),
    inference(global_subsumption,[],[f331])).

fof(f331,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f330,f225])).

fof(f225,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f223])).

fof(f223,plain,
    ( spl4_3
  <=> k1_xboole_0 = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f330,plain,(
    k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f329,f153])).

fof(f329,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(forward_demodulation,[],[f320,f107])).

fof(f320,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(superposition,[],[f64,f106])).

fof(f3301,plain,
    ( sK3 = k2_relat_1(sK2)
    | ~ spl4_135 ),
    inference(avatar_component_clause,[],[f3299])).

fof(f3299,plain,
    ( spl4_135
  <=> sK3 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_135])])).

fof(f3768,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_relat_1(k1_xboole_0),k1_xboole_0,sK3) != k7_relset_1(k2_relat_1(k1_xboole_0),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(k1_xboole_0),k1_xboole_0),sK3)
    | ~ spl4_5 ),
    inference(superposition,[],[f911,f398])).

fof(f911,plain,(
    k8_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK3) != k7_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2),sK3) ),
    inference(forward_demodulation,[],[f910,f106])).

fof(f910,plain,(
    k8_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2,sK3) != k7_relset_1(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2),sK3) ),
    inference(forward_demodulation,[],[f340,f909])).

fof(f340,plain,(
    k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k7_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) ),
    inference(superposition,[],[f66,f107])).

fof(f66,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f5977,plain,
    ( ~ spl4_5
    | spl4_10
    | ~ spl4_113 ),
    inference(avatar_contradiction_clause,[],[f5972])).

fof(f5972,plain,
    ( $false
    | ~ spl4_5
    | spl4_10
    | ~ spl4_113 ),
    inference(resolution,[],[f5777,f754])).

fof(f754,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_funct_1(sK2))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f752])).

fof(f752,plain,
    ( spl4_10
  <=> r1_tarski(k1_xboole_0,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f5777,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl4_5
    | ~ spl4_113 ),
    inference(resolution,[],[f5735,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f3857,plain,
    ( ~ spl4_3
    | ~ spl4_5
    | spl4_112
    | ~ spl4_135 ),
    inference(avatar_contradiction_clause,[],[f3856])).

fof(f3856,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_5
    | spl4_112
    | ~ spl4_135 ),
    inference(subsumption_resolution,[],[f3855,f2781])).

fof(f2781,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(k1_xboole_0))
    | spl4_112 ),
    inference(avatar_component_clause,[],[f2779])).

fof(f2779,plain,
    ( spl4_112
  <=> r1_tarski(k1_xboole_0,k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_112])])).

fof(f3855,plain,
    ( r1_tarski(k1_xboole_0,k2_relat_1(k1_xboole_0))
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_135 ),
    inference(forward_demodulation,[],[f3776,f3658])).

fof(f3776,plain,
    ( r1_tarski(sK3,k2_relat_1(k1_xboole_0))
    | ~ spl4_5 ),
    inference(superposition,[],[f1178,f398])).

fof(f1178,plain,(
    r1_tarski(sK3,k2_relat_1(sK2)) ),
    inference(superposition,[],[f111,f909])).

fof(f111,plain,(
    r1_tarski(sK3,k2_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f108,f107])).

fof(f108,plain,(
    r1_tarski(sK3,u1_struct_0(sK1)) ),
    inference(resolution,[],[f78,f63])).

fof(f63,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f52])).

fof(f3657,plain,
    ( ~ spl4_1
    | ~ spl4_3
    | spl4_134 ),
    inference(avatar_contradiction_clause,[],[f3656])).

fof(f3656,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_3
    | spl4_134 ),
    inference(global_subsumption,[],[f3628,f3638])).

fof(f3638,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | ~ spl4_3
    | spl4_134 ),
    inference(forward_demodulation,[],[f3297,f3308])).

fof(f3297,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK3)
    | spl4_134 ),
    inference(avatar_component_clause,[],[f3295])).

fof(f3295,plain,
    ( spl4_134
  <=> r1_tarski(k2_relat_1(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_134])])).

fof(f3628,plain,
    ( r1_tarski(k1_xboole_0,sK3)
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f3627,f3308])).

fof(f3627,plain,
    ( r1_tarski(k2_relat_1(sK2),sK3)
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f141,f909])).

fof(f141,plain,
    ( r1_tarski(k2_struct_0(sK1),sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl4_1
  <=> r1_tarski(k2_struct_0(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f3302,plain,
    ( ~ spl4_134
    | spl4_135 ),
    inference(avatar_split_clause,[],[f1223,f3299,f3295])).

fof(f1223,plain,
    ( sK3 = k2_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),sK3) ),
    inference(resolution,[],[f1178,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f3293,plain,
    ( ~ spl4_4
    | ~ spl4_14 ),
    inference(avatar_contradiction_clause,[],[f3292])).

fof(f3292,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f3291,f1012])).

fof(f1012,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f1011,f130])).

fof(f130,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f129,f115])).

fof(f129,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f128,f60])).

fof(f128,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f74,f65])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1011,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f994,f229])).

fof(f229,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl4_4
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f994,plain,(
    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(resolution,[],[f924,f85])).

fof(f3291,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl4_4
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f3290,f982])).

fof(f982,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl4_4 ),
    inference(superposition,[],[f923,f229])).

fof(f3290,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | ~ spl4_4
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f3289,f2412])).

fof(f2412,plain,
    ( k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK3) != k7_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2),sK3)
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f2410,f982])).

fof(f2410,plain,
    ( k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK3) != k7_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),sK3)
    | ~ spl4_4 ),
    inference(superposition,[],[f911,f229])).

fof(f3289,plain,
    ( k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK3) = k7_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2),sK3)
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | ~ spl4_4
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f3288,f1091])).

fof(f1091,plain,
    ( sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl4_4
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f1090,f122])).

fof(f122,plain,(
    sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f121,f115])).

fof(f121,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f120,f60])).

fof(f120,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f72,f65])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(f1090,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl4_4
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f1089,f229])).

fof(f1089,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f1088,f923])).

fof(f1088,plain,
    ( k2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f872,f909])).

fof(f872,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f870])).

fof(f870,plain,
    ( spl4_14
  <=> k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f3288,plain,
    ( k7_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2),sK3) = k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK3)
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f3287,f982])).

fof(f3287,plain,
    ( k7_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),sK3) = k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK3)
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f3286,f969])).

fof(f969,plain,
    ( v1_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f961,f909])).

fof(f961,plain,
    ( v1_funct_1(k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2))
    | ~ spl4_4 ),
    inference(superposition,[],[f193,f229])).

fof(f193,plain,(
    v1_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(forward_demodulation,[],[f192,f106])).

fof(f192,plain,(
    v1_funct_1(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(forward_demodulation,[],[f191,f107])).

fof(f191,plain,(
    v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f190,f60])).

fof(f190,plain,
    ( v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f186,f61])).

fof(f186,plain,
    ( v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f90,f62])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_tops_2(X0,X1,X2))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f3286,plain,
    ( k7_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),sK3) = k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK3)
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | ~ v1_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f3285,f975])).

fof(f975,plain,
    ( v2_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | ~ spl4_4 ),
    inference(superposition,[],[f921,f229])).

fof(f921,plain,(
    v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    inference(forward_demodulation,[],[f920,f106])).

fof(f920,plain,(
    v2_funct_1(k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    inference(forward_demodulation,[],[f294,f909])).

fof(f294,plain,(
    v2_funct_1(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(forward_demodulation,[],[f293,f107])).

fof(f293,plain,(
    v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f292,f58])).

fof(f292,plain,
    ( v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f291,f59])).

fof(f291,plain,
    ( v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f290,f60])).

fof(f290,plain,
    ( v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_1(sK2)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f289,f61])).

fof(f289,plain,
    ( v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f288,f64])).

fof(f288,plain,
    ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f286,f65])).

fof(f286,plain,
    ( ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f70,f62])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_tops_2)).

fof(f3285,plain,
    ( k7_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),sK3) = k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK3)
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | ~ v2_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | ~ v1_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f3271,f970])).

fof(f970,plain,
    ( v1_funct_2(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f962,f909])).

fof(f962,plain,
    ( v1_funct_2(k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2),k2_struct_0(sK1),k1_relat_1(sK2))
    | ~ spl4_4 ),
    inference(superposition,[],[f201,f229])).

fof(f201,plain,(
    v1_funct_2(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k2_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f200,f107])).

fof(f200,plain,(
    v1_funct_2(k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f199,f106])).

fof(f199,plain,(
    v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f198,f60])).

fof(f198,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f194,f61])).

fof(f194,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f91,f62])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f3271,plain,
    ( k7_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),sK3) = k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK3)
    | ~ v1_funct_2(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | ~ v2_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | ~ v1_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | ~ spl4_4 ),
    inference(resolution,[],[f1117,f971])).

fof(f971,plain,
    ( m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f963,f909])).

fof(f963,plain,
    ( m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2))))
    | ~ spl4_4 ),
    inference(superposition,[],[f209,f229])).

fof(f209,plain,(
    m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f208,f107])).

fof(f208,plain,(
    m1_subset_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f207,f106])).

fof(f207,plain,(
    m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f206,f60])).

fof(f206,plain,
    ( m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f202,f61])).

fof(f202,plain,
    ( m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f92,f62])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1117,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
        | k7_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),X0,sK3) = k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),X0),sK3)
        | ~ v1_funct_2(X0,k2_relat_1(sK2),k1_relat_1(sK2))
        | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),X0)
        | ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0) )
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f1116,f229])).

fof(f1116,plain,
    ( ! [X0] :
        ( k7_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),X0,sK3) = k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),X0),sK3)
        | ~ v1_funct_2(X0,k2_relat_1(sK2),k1_relat_1(sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
        | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),X0)
        | ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0) )
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f1115,f229])).

fof(f1115,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,k2_relat_1(sK2),k1_relat_1(sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
        | k7_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),X0,sK3) = k8_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),X0),sK3)
        | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),X0)
        | ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0) )
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f1114,f229])).

fof(f1114,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
        | ~ v1_funct_2(X0,k2_relat_1(sK2),k2_struct_0(sK0))
        | k7_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),X0,sK3) = k8_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),X0),sK3)
        | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),X0)
        | ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0) )
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f1113,f229])).

fof(f1113,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
      | ~ v1_funct_2(X0,k2_relat_1(sK2),k2_struct_0(sK0))
      | k7_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),X0,sK3) = k8_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),X0),sK3)
      | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f1108,f58])).

fof(f1108,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
      | ~ v1_funct_2(X0,k2_relat_1(sK2),k2_struct_0(sK0))
      | k7_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),X0,sK3) = k8_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),X0),sK3)
      | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ l1_struct_0(sK0) ) ),
    inference(superposition,[],[f919,f106])).

fof(f919,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),u1_struct_0(X1))))
      | ~ v1_funct_2(X0,k2_relat_1(sK2),u1_struct_0(X1))
      | k7_relset_1(k2_relat_1(sK2),u1_struct_0(X1),X0,sK3) = k8_relset_1(u1_struct_0(X1),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),u1_struct_0(X1),X0),sK3)
      | k2_struct_0(X1) != k2_relset_1(k2_relat_1(sK2),u1_struct_0(X1),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ l1_struct_0(X1) ) ),
    inference(forward_demodulation,[],[f918,f909])).

fof(f918,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X0,k2_struct_0(sK1),u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),u1_struct_0(X1))))
      | k7_relset_1(k2_relat_1(sK2),u1_struct_0(X1),X0,sK3) = k8_relset_1(u1_struct_0(X1),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),u1_struct_0(X1),X0),sK3)
      | k2_struct_0(X1) != k2_relset_1(k2_relat_1(sK2),u1_struct_0(X1),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ l1_struct_0(X1) ) ),
    inference(forward_demodulation,[],[f917,f107])).

fof(f917,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),u1_struct_0(X1))))
      | k7_relset_1(k2_relat_1(sK2),u1_struct_0(X1),X0,sK3) = k8_relset_1(u1_struct_0(X1),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),u1_struct_0(X1),X0),sK3)
      | k2_struct_0(X1) != k2_relset_1(k2_relat_1(sK2),u1_struct_0(X1),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_struct_0(X1) ) ),
    inference(forward_demodulation,[],[f916,f909])).

fof(f916,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X1))))
      | k7_relset_1(k2_relat_1(sK2),u1_struct_0(X1),X0,sK3) = k8_relset_1(u1_struct_0(X1),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),u1_struct_0(X1),X0),sK3)
      | k2_struct_0(X1) != k2_relset_1(k2_relat_1(sK2),u1_struct_0(X1),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_struct_0(X1) ) ),
    inference(forward_demodulation,[],[f915,f107])).

fof(f915,plain,(
    ! [X0,X1] :
      ( k7_relset_1(k2_relat_1(sK2),u1_struct_0(X1),X0,sK3) = k8_relset_1(u1_struct_0(X1),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),u1_struct_0(X1),X0),sK3)
      | k2_struct_0(X1) != k2_relset_1(k2_relat_1(sK2),u1_struct_0(X1),X0)
      | ~ v2_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_struct_0(X1) ) ),
    inference(forward_demodulation,[],[f914,f909])).

fof(f914,plain,(
    ! [X0,X1] :
      ( k7_relset_1(k2_struct_0(sK1),u1_struct_0(X1),X0,sK3) = k8_relset_1(u1_struct_0(X1),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(X1),X0),sK3)
      | k2_struct_0(X1) != k2_relset_1(k2_relat_1(sK2),u1_struct_0(X1),X0)
      | ~ v2_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_struct_0(X1) ) ),
    inference(forward_demodulation,[],[f913,f107])).

fof(f913,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X1) != k2_relset_1(k2_relat_1(sK2),u1_struct_0(X1),X0)
      | ~ v2_funct_1(X0)
      | k7_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X0,sK3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X0),sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_struct_0(X1) ) ),
    inference(forward_demodulation,[],[f302,f909])).

fof(f302,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X1) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(X1),X0)
      | ~ v2_funct_1(X0)
      | k7_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X0,sK3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X0),sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_struct_0(X1) ) ),
    inference(forward_demodulation,[],[f301,f107])).

fof(f301,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X0)
      | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X0)
      | k7_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X0,sK3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X0),sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f299,f59])).

fof(f299,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X0)
      | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X0)
      | k7_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X0,sK3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X0),sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(sK1) ) ),
    inference(resolution,[],[f71,f63])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  | ~ v2_funct_1(X2)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  | ~ v2_funct_1(X2)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( v2_funct_1(X2)
                      & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                   => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tops_2)).

fof(f2786,plain,
    ( ~ spl4_112
    | spl4_113 ),
    inference(avatar_split_clause,[],[f2776,f2783,f2779])).

fof(f2776,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f1509,f77])).

fof(f1509,plain,(
    r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f555,f78])).

fof(f555,plain,(
    m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f169,f101])).

fof(f169,plain,(
    ! [X0,X1] : m1_subset_1(k2_relat_1(k2_zfmisc_1(X0,X1)),k1_zfmisc_1(X1)) ),
    inference(forward_demodulation,[],[f163,f149])).

fof(f149,plain,(
    ! [X0,X1] : k2_relset_1(X0,X1,k2_zfmisc_1(X0,X1)) = k2_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(resolution,[],[f85,f104])).

fof(f163,plain,(
    ! [X0,X1] : m1_subset_1(k2_relset_1(X0,X1,k2_zfmisc_1(X0,X1)),k1_zfmisc_1(X1)) ),
    inference(resolution,[],[f87,f104])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f1014,plain,
    ( ~ spl4_4
    | spl4_15 ),
    inference(avatar_contradiction_clause,[],[f1013])).

fof(f1013,plain,
    ( $false
    | ~ spl4_4
    | spl4_15 ),
    inference(subsumption_resolution,[],[f1012,f944])).

fof(f944,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl4_4
    | spl4_15 ),
    inference(forward_demodulation,[],[f943,f229])).

fof(f943,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | spl4_15 ),
    inference(forward_demodulation,[],[f942,f923])).

fof(f942,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | spl4_15 ),
    inference(forward_demodulation,[],[f876,f909])).

fof(f876,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | spl4_15 ),
    inference(avatar_component_clause,[],[f874])).

fof(f874,plain,
    ( spl4_15
  <=> k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f941,plain,(
    spl4_16 ),
    inference(avatar_contradiction_clause,[],[f940])).

fof(f940,plain,
    ( $false
    | spl4_16 ),
    inference(subsumption_resolution,[],[f939,f921])).

fof(f939,plain,
    ( ~ v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | spl4_16 ),
    inference(forward_demodulation,[],[f880,f909])).

fof(f880,plain,
    ( ~ v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | spl4_16 ),
    inference(avatar_component_clause,[],[f878])).

fof(f878,plain,
    ( spl4_16
  <=> v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f881,plain,
    ( spl4_14
    | ~ spl4_15
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f486,f878,f874,f870])).

fof(f486,plain,
    ( ~ v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f485,f193])).

fof(f485,plain,
    ( ~ v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ v1_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f432,f201])).

fof(f432,plain,
    ( ~ v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ v1_funct_2(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ v1_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(resolution,[],[f209,f96])).

fof(f859,plain,
    ( spl4_1
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f854])).

fof(f854,plain,
    ( $false
    | spl4_1
    | ~ spl4_3 ),
    inference(resolution,[],[f772,f232])).

fof(f232,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | spl4_1
    | ~ spl4_3 ),
    inference(superposition,[],[f142,f225])).

fof(f142,plain,
    ( ~ r1_tarski(k2_struct_0(sK1),sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f140])).

fof(f772,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl4_3 ),
    inference(resolution,[],[f611,f78])).

fof(f611,plain,
    ( ! [X3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f606,f578])).

fof(f578,plain,
    ( ! [X3] : k1_xboole_0 = k1_relset_1(X3,k1_xboole_0,k2_funct_1(sK2))
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f577,f331])).

fof(f577,plain,
    ( ! [X3] : k2_relat_1(sK2) = k1_relset_1(X3,k1_xboole_0,k2_funct_1(sK2))
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f574,f127])).

fof(f574,plain,
    ( ! [X3] : k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(X3,k1_xboole_0,k2_funct_1(sK2))
    | ~ spl4_3 ),
    inference(resolution,[],[f133,f269])).

fof(f269,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f268,f102])).

fof(f268,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f267,f225])).

fof(f606,plain,
    ( ! [X3] : m1_subset_1(k1_relset_1(X3,k1_xboole_0,k2_funct_1(sK2)),k1_zfmisc_1(X3))
    | ~ spl4_3 ),
    inference(resolution,[],[f156,f269])).

fof(f858,plain,
    ( ~ spl4_3
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f855])).

fof(f855,plain,
    ( $false
    | ~ spl4_3
    | spl4_6 ),
    inference(resolution,[],[f772,f402])).

fof(f402,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f400])).

fof(f400,plain,
    ( spl4_6
  <=> r1_tarski(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f759,plain,
    ( ~ spl4_10
    | spl4_11
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f749,f223,f756,f752])).

fof(f749,plain,
    ( k1_xboole_0 = k2_funct_1(sK2)
    | ~ r1_tarski(k1_xboole_0,k2_funct_1(sK2))
    | ~ spl4_3 ),
    inference(resolution,[],[f378,f77])).

fof(f378,plain,
    ( r1_tarski(k2_funct_1(sK2),k1_xboole_0)
    | ~ spl4_3 ),
    inference(resolution,[],[f269,f78])).

fof(f403,plain,
    ( spl4_5
    | ~ spl4_6
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f394,f223,f400,f396])).

fof(f394,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | k1_xboole_0 = sK2
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f393,f101])).

fof(f393,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0),sK2)
    | k1_xboole_0 = sK2
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f392,f225])).

fof(f392,plain,
    ( k1_xboole_0 = sK2
    | ~ r1_tarski(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)),sK2)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f391,f101])).

fof(f391,plain,
    ( sK2 = k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)
    | ~ r1_tarski(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)),sK2)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f388,f225])).

fof(f388,plain,
    ( sK2 = k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ r1_tarski(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)),sK2) ),
    inference(resolution,[],[f113,f77])).

fof(f113,plain,(
    r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f112,f106])).

fof(f112,plain,(
    r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f109,f107])).

fof(f109,plain,(
    r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(resolution,[],[f78,f62])).

fof(f230,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f221,f227,f223])).

fof(f221,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k1_xboole_0 = k2_struct_0(sK1) ),
    inference(forward_demodulation,[],[f220,f184])).

fof(f184,plain,(
    k1_relat_1(sK2) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f183,f136])).

fof(f136,plain,(
    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(forward_demodulation,[],[f135,f106])).

fof(f135,plain,(
    k1_relat_1(sK2) = k1_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(forward_demodulation,[],[f131,f107])).

fof(f131,plain,(
    k1_relat_1(sK2) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(resolution,[],[f84,f62])).

fof(f183,plain,(
    k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f182,f106])).

fof(f182,plain,(
    k1_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f178,f107])).

fof(f178,plain,(
    k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK1)) ),
    inference(resolution,[],[f89,f62])).

fof(f220,plain,
    ( k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | k1_xboole_0 = k2_struct_0(sK1) ),
    inference(forward_demodulation,[],[f219,f106])).

fof(f219,plain,
    ( u1_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | k1_xboole_0 = k2_struct_0(sK1) ),
    inference(forward_demodulation,[],[f218,f107])).

fof(f218,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | u1_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f217,f107])).

fof(f217,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | u1_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f216,f60])).

fof(f216,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | u1_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f212,f61])).

fof(f212,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | u1_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK1))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f97,f62])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k8_relset_1(X0,X1,X2,X1) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:45:35 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.49  % (29208)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.50  % (29207)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.50  % (29209)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (29217)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (29210)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (29218)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (29222)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.17/0.52  % (29213)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.17/0.52  % (29226)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.17/0.52  % (29228)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.17/0.52  % (29227)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.17/0.52  % (29205)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.17/0.52  % (29224)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.17/0.52  % (29214)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.17/0.53  % (29212)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.17/0.53  % (29206)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.17/0.53  % (29215)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.17/0.53  % (29219)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.34/0.53  % (29225)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.34/0.54  % (29223)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.34/0.54  % (29221)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.34/0.54  % (29204)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.34/0.54  % (29229)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.34/0.55  % (29216)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.34/0.55  % (29220)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.34/0.55  % (29211)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.34/0.62  % (29213)Refutation not found, incomplete strategy% (29213)------------------------------
% 1.34/0.62  % (29213)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.62  % (29213)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.62  
% 1.34/0.62  % (29213)Memory used [KB]: 6268
% 1.34/0.62  % (29213)Time elapsed: 0.193 s
% 1.34/0.62  % (29213)------------------------------
% 1.34/0.62  % (29213)------------------------------
% 3.68/0.86  % (29214)Refutation found. Thanks to Tanya!
% 3.68/0.86  % SZS status Theorem for theBenchmark
% 3.68/0.86  % SZS output start Proof for theBenchmark
% 3.68/0.86  fof(f6844,plain,(
% 3.68/0.86    $false),
% 3.68/0.86    inference(avatar_sat_refutation,[],[f230,f403,f759,f858,f859,f881,f941,f1014,f2786,f3293,f3302,f3657,f3857,f5977,f6843])).
% 3.68/0.86  fof(f6843,plain,(
% 3.68/0.86    ~spl4_3 | ~spl4_5 | ~spl4_11 | ~spl4_113 | ~spl4_135),
% 3.68/0.86    inference(avatar_contradiction_clause,[],[f6842])).
% 3.68/0.86  fof(f6842,plain,(
% 3.68/0.86    $false | (~spl4_3 | ~spl4_5 | ~spl4_11 | ~spl4_113 | ~spl4_135)),
% 3.68/0.86    inference(subsumption_resolution,[],[f6841,f6003])).
% 3.68/0.86  fof(f6003,plain,(
% 3.68/0.86    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl4_5 | ~spl4_11 | ~spl4_113)),
% 3.68/0.86    inference(superposition,[],[f3963,f5991])).
% 3.68/0.86  fof(f5991,plain,(
% 3.68/0.86    k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl4_5 | ~spl4_11)),
% 3.68/0.86    inference(forward_demodulation,[],[f758,f398])).
% 3.68/0.86  fof(f398,plain,(
% 3.68/0.86    k1_xboole_0 = sK2 | ~spl4_5),
% 3.68/0.86    inference(avatar_component_clause,[],[f396])).
% 3.68/0.86  fof(f396,plain,(
% 3.68/0.86    spl4_5 <=> k1_xboole_0 = sK2),
% 3.68/0.86    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 3.68/0.86  fof(f758,plain,(
% 3.68/0.86    k1_xboole_0 = k2_funct_1(sK2) | ~spl4_11),
% 3.68/0.86    inference(avatar_component_clause,[],[f756])).
% 3.68/0.86  fof(f756,plain,(
% 3.68/0.86    spl4_11 <=> k1_xboole_0 = k2_funct_1(sK2)),
% 3.68/0.86    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 3.68/0.86  fof(f3963,plain,(
% 3.68/0.86    k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) | (~spl4_5 | ~spl4_113)),
% 3.68/0.86    inference(forward_demodulation,[],[f3739,f2785])).
% 3.68/0.86  fof(f2785,plain,(
% 3.68/0.86    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl4_113),
% 3.68/0.86    inference(avatar_component_clause,[],[f2783])).
% 3.68/0.86  fof(f2783,plain,(
% 3.68/0.86    spl4_113 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.68/0.86    introduced(avatar_definition,[new_symbols(naming,[spl4_113])])).
% 3.68/0.86  fof(f3739,plain,(
% 3.68/0.86    k2_relat_1(k1_xboole_0) = k1_relat_1(k2_funct_1(k1_xboole_0)) | ~spl4_5),
% 3.68/0.86    inference(superposition,[],[f127,f398])).
% 3.68/0.86  fof(f127,plain,(
% 3.68/0.86    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 3.68/0.86    inference(subsumption_resolution,[],[f126,f115])).
% 3.68/0.86  fof(f115,plain,(
% 3.68/0.86    v1_relat_1(sK2)),
% 3.68/0.86    inference(resolution,[],[f83,f62])).
% 3.68/0.86  fof(f62,plain,(
% 3.68/0.86    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.68/0.86    inference(cnf_transformation,[],[f52])).
% 3.68/0.86  fof(f52,plain,(
% 3.68/0.86    (((k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 3.68/0.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f51,f50,f49,f48])).
% 3.68/0.86  fof(f48,plain,(
% 3.68/0.86    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X3) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 3.68/0.86    introduced(choice_axiom,[])).
% 3.68/0.86  fof(f49,plain,(
% 3.68/0.86    ? [X1] : (? [X2] : (? [X3] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X3) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (? [X3] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))),
% 3.68/0.86    introduced(choice_axiom,[])).
% 3.68/0.86  fof(f50,plain,(
% 3.68/0.86    ? [X2] : (? [X3] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (? [X3] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X3) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 3.68/0.86    introduced(choice_axiom,[])).
% 3.68/0.86  fof(f51,plain,(
% 3.68/0.86    ? [X3] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X3) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) => (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))))),
% 3.68/0.86    introduced(choice_axiom,[])).
% 3.68/0.86  fof(f24,plain,(
% 3.68/0.86    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 3.68/0.86    inference(flattening,[],[f23])).
% 3.68/0.86  fof(f23,plain,(
% 3.68/0.86    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 3.68/0.86    inference(ennf_transformation,[],[f22])).
% 3.68/0.86  fof(f22,negated_conjecture,(
% 3.68/0.86    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3))))))),
% 3.68/0.86    inference(negated_conjecture,[],[f21])).
% 3.68/0.86  fof(f21,conjecture,(
% 3.68/0.86    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3))))))),
% 3.68/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_tops_2)).
% 3.68/0.86  fof(f83,plain,(
% 3.68/0.86    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 3.68/0.86    inference(cnf_transformation,[],[f34])).
% 3.68/0.86  fof(f34,plain,(
% 3.68/0.86    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.68/0.86    inference(ennf_transformation,[],[f8])).
% 3.68/0.86  fof(f8,axiom,(
% 3.68/0.86    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.68/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 3.68/0.86  fof(f126,plain,(
% 3.68/0.86    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 3.68/0.86    inference(subsumption_resolution,[],[f125,f60])).
% 3.68/0.86  fof(f60,plain,(
% 3.68/0.86    v1_funct_1(sK2)),
% 3.68/0.86    inference(cnf_transformation,[],[f52])).
% 3.68/0.86  fof(f125,plain,(
% 3.68/0.86    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 3.68/0.86    inference(resolution,[],[f73,f65])).
% 3.68/0.86  fof(f65,plain,(
% 3.68/0.86    v2_funct_1(sK2)),
% 3.68/0.86    inference(cnf_transformation,[],[f52])).
% 3.68/0.86  fof(f73,plain,(
% 3.68/0.86    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.68/0.86    inference(cnf_transformation,[],[f33])).
% 3.68/0.86  fof(f33,plain,(
% 3.68/0.86    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.68/0.86    inference(flattening,[],[f32])).
% 3.68/0.86  fof(f32,plain,(
% 3.68/0.86    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.68/0.86    inference(ennf_transformation,[],[f6])).
% 3.68/0.86  fof(f6,axiom,(
% 3.68/0.86    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 3.68/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 3.68/0.86  fof(f6841,plain,(
% 3.68/0.86    k1_xboole_0 != k1_relat_1(k1_xboole_0) | (~spl4_3 | ~spl4_5 | ~spl4_11 | ~spl4_113 | ~spl4_135)),
% 3.68/0.86    inference(forward_demodulation,[],[f6840,f5826])).
% 3.68/0.86  fof(f5826,plain,(
% 3.68/0.86    ( ! [X10,X9] : (k1_xboole_0 = k7_relset_1(X9,X10,k1_xboole_0,X9)) ) | (~spl4_5 | ~spl4_113)),
% 3.68/0.86    inference(forward_demodulation,[],[f5783,f5823])).
% 3.68/0.86  fof(f5823,plain,(
% 3.68/0.86    ( ! [X4,X3] : (k1_xboole_0 = k2_relset_1(X3,X4,k1_xboole_0)) ) | (~spl4_5 | ~spl4_113)),
% 3.68/0.86    inference(forward_demodulation,[],[f5780,f2785])).
% 3.68/0.86  fof(f5780,plain,(
% 3.68/0.86    ( ! [X4,X3] : (k2_relat_1(k1_xboole_0) = k2_relset_1(X3,X4,k1_xboole_0)) ) | (~spl4_5 | ~spl4_113)),
% 3.68/0.86    inference(resolution,[],[f5735,f85])).
% 3.68/0.86  fof(f85,plain,(
% 3.68/0.86    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 3.68/0.86    inference(cnf_transformation,[],[f36])).
% 3.68/0.86  fof(f36,plain,(
% 3.68/0.86    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.68/0.86    inference(ennf_transformation,[],[f12])).
% 3.68/0.86  fof(f12,axiom,(
% 3.68/0.86    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 3.68/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 3.68/0.86  fof(f5735,plain,(
% 3.68/0.86    ( ! [X4] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X4))) ) | (~spl4_5 | ~spl4_113)),
% 3.68/0.86    inference(forward_demodulation,[],[f5722,f5731])).
% 3.68/0.86  fof(f5731,plain,(
% 3.68/0.86    ( ! [X0] : (k1_xboole_0 = k1_relset_1(X0,k1_xboole_0,k2_funct_1(k1_xboole_0))) ) | (~spl4_5 | ~spl4_113)),
% 3.68/0.86    inference(forward_demodulation,[],[f5718,f3963])).
% 3.68/0.86  fof(f5718,plain,(
% 3.68/0.86    ( ! [X0] : (k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_relset_1(X0,k1_xboole_0,k2_funct_1(k1_xboole_0))) ) | (~spl4_5 | ~spl4_113)),
% 3.68/0.86    inference(resolution,[],[f3947,f133])).
% 3.68/0.86  fof(f133,plain,(
% 3.68/0.86    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | k1_relset_1(X0,k1_xboole_0,X1) = k1_relat_1(X1)) )),
% 3.68/0.86    inference(superposition,[],[f84,f101])).
% 3.68/0.86  fof(f101,plain,(
% 3.68/0.86    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.68/0.86    inference(equality_resolution,[],[f82])).
% 3.68/0.86  fof(f82,plain,(
% 3.68/0.86    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 3.68/0.86    inference(cnf_transformation,[],[f57])).
% 3.68/0.86  fof(f57,plain,(
% 3.68/0.86    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.68/0.86    inference(flattening,[],[f56])).
% 3.68/0.86  fof(f56,plain,(
% 3.68/0.86    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.68/0.86    inference(nnf_transformation,[],[f2])).
% 3.68/0.86  fof(f2,axiom,(
% 3.68/0.86    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.68/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 3.68/0.86  fof(f84,plain,(
% 3.68/0.86    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 3.68/0.86    inference(cnf_transformation,[],[f35])).
% 3.68/0.86  fof(f35,plain,(
% 3.68/0.86    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.68/0.86    inference(ennf_transformation,[],[f11])).
% 3.68/0.86  fof(f11,axiom,(
% 3.68/0.86    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 3.68/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 3.68/0.86  fof(f3947,plain,(
% 3.68/0.86    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl4_5 | ~spl4_113)),
% 3.68/0.86    inference(forward_demodulation,[],[f3946,f102])).
% 3.68/0.86  fof(f102,plain,(
% 3.68/0.86    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.68/0.86    inference(equality_resolution,[],[f81])).
% 3.68/0.86  fof(f81,plain,(
% 3.68/0.86    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 3.68/0.86    inference(cnf_transformation,[],[f57])).
% 3.68/0.86  fof(f3946,plain,(
% 3.68/0.86    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | (~spl4_5 | ~spl4_113)),
% 3.68/0.86    inference(forward_demodulation,[],[f3772,f2785])).
% 3.68/0.86  fof(f3772,plain,(
% 3.68/0.86    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(k1_xboole_0),k2_struct_0(sK0)))) | ~spl4_5),
% 3.68/0.86    inference(superposition,[],[f924,f398])).
% 3.68/0.86  fof(f924,plain,(
% 3.68/0.86    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))),
% 3.68/0.86    inference(forward_demodulation,[],[f267,f909])).
% 3.68/0.86  fof(f909,plain,(
% 3.68/0.86    k2_struct_0(sK1) = k2_relat_1(sK2)),
% 3.68/0.86    inference(forward_demodulation,[],[f908,f153])).
% 3.68/0.86  fof(f153,plain,(
% 3.68/0.86    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 3.68/0.86    inference(forward_demodulation,[],[f152,f106])).
% 3.68/0.86  fof(f106,plain,(
% 3.68/0.86    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 3.68/0.86    inference(resolution,[],[f69,f58])).
% 3.68/0.86  fof(f58,plain,(
% 3.68/0.86    l1_struct_0(sK0)),
% 3.68/0.86    inference(cnf_transformation,[],[f52])).
% 3.68/0.86  fof(f69,plain,(
% 3.68/0.86    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 3.68/0.86    inference(cnf_transformation,[],[f25])).
% 3.68/0.86  fof(f25,plain,(
% 3.68/0.86    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.68/0.86    inference(ennf_transformation,[],[f16])).
% 3.68/0.86  fof(f16,axiom,(
% 3.68/0.86    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.68/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 3.68/0.86  fof(f152,plain,(
% 3.68/0.86    k2_relat_1(sK2) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 3.68/0.86    inference(forward_demodulation,[],[f148,f107])).
% 3.68/0.86  fof(f107,plain,(
% 3.68/0.86    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 3.68/0.86    inference(resolution,[],[f69,f59])).
% 3.68/0.86  fof(f59,plain,(
% 3.68/0.86    l1_struct_0(sK1)),
% 3.68/0.86    inference(cnf_transformation,[],[f52])).
% 3.68/0.86  fof(f148,plain,(
% 3.68/0.86    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2)),
% 3.68/0.86    inference(resolution,[],[f85,f62])).
% 3.68/0.86  fof(f908,plain,(
% 3.68/0.86    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 3.68/0.86    inference(forward_demodulation,[],[f341,f106])).
% 3.68/0.86  fof(f341,plain,(
% 3.68/0.86    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 3.68/0.86    inference(superposition,[],[f64,f107])).
% 3.68/0.86  fof(f64,plain,(
% 3.68/0.86    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 3.68/0.86    inference(cnf_transformation,[],[f52])).
% 3.68/0.86  fof(f267,plain,(
% 3.68/0.86    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 3.68/0.86    inference(forward_demodulation,[],[f266,f107])).
% 3.68/0.86  fof(f266,plain,(
% 3.68/0.86    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK0))))),
% 3.68/0.86    inference(forward_demodulation,[],[f265,f106])).
% 3.68/0.86  fof(f265,plain,(
% 3.68/0.86    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 3.68/0.86    inference(subsumption_resolution,[],[f264,f107])).
% 3.68/0.86  fof(f264,plain,(
% 3.68/0.86    u1_struct_0(sK1) != k2_struct_0(sK1) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 3.68/0.86    inference(forward_demodulation,[],[f263,f64])).
% 3.68/0.86  fof(f263,plain,(
% 3.68/0.86    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 3.68/0.86    inference(subsumption_resolution,[],[f262,f60])).
% 3.68/0.86  fof(f262,plain,(
% 3.68/0.86    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(sK2)),
% 3.68/0.86    inference(subsumption_resolution,[],[f261,f61])).
% 3.68/0.86  fof(f61,plain,(
% 3.68/0.86    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.68/0.86    inference(cnf_transformation,[],[f52])).
% 3.68/0.86  fof(f261,plain,(
% 3.68/0.86    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 3.68/0.86    inference(subsumption_resolution,[],[f257,f65])).
% 3.68/0.86  fof(f257,plain,(
% 3.68/0.86    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 3.68/0.86    inference(resolution,[],[f95,f62])).
% 3.68/0.86  fof(f95,plain,(
% 3.68/0.86    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.68/0.86    inference(cnf_transformation,[],[f43])).
% 3.68/0.86  fof(f43,plain,(
% 3.68/0.86    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.68/0.86    inference(flattening,[],[f42])).
% 3.68/0.86  fof(f42,plain,(
% 3.68/0.86    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.68/0.86    inference(ennf_transformation,[],[f14])).
% 3.68/0.86  fof(f14,axiom,(
% 3.68/0.86    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.68/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 3.68/0.86  fof(f5722,plain,(
% 3.68/0.86    ( ! [X4] : (m1_subset_1(k1_relset_1(X4,k1_xboole_0,k2_funct_1(k1_xboole_0)),k1_zfmisc_1(X4))) ) | (~spl4_5 | ~spl4_113)),
% 3.68/0.86    inference(resolution,[],[f3947,f156])).
% 3.68/0.86  fof(f156,plain,(
% 3.68/0.86    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | m1_subset_1(k1_relset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X0))) )),
% 3.68/0.86    inference(superposition,[],[f86,f101])).
% 3.68/0.86  fof(f86,plain,(
% 3.68/0.86    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 3.68/0.86    inference(cnf_transformation,[],[f37])).
% 3.68/0.86  fof(f37,plain,(
% 3.68/0.86    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.68/0.86    inference(ennf_transformation,[],[f9])).
% 3.68/0.86  fof(f9,axiom,(
% 3.68/0.86    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.68/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 3.68/0.86  fof(f5783,plain,(
% 3.68/0.86    ( ! [X10,X9] : (k2_relset_1(X9,X10,k1_xboole_0) = k7_relset_1(X9,X10,k1_xboole_0,X9)) ) | (~spl4_5 | ~spl4_113)),
% 3.68/0.86    inference(resolution,[],[f5735,f88])).
% 3.68/0.86  fof(f88,plain,(
% 3.68/0.86    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) )),
% 3.68/0.86    inference(cnf_transformation,[],[f39])).
% 3.68/0.86  fof(f39,plain,(
% 3.68/0.86    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.68/0.86    inference(ennf_transformation,[],[f13])).
% 3.68/0.86  fof(f13,axiom,(
% 3.68/0.86    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 3.68/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 3.68/0.86  fof(f6840,plain,(
% 3.68/0.86    k1_relat_1(k1_xboole_0) != k7_relset_1(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0,k1_xboole_0) | (~spl4_3 | ~spl4_5 | ~spl4_11 | ~spl4_113 | ~spl4_135)),
% 3.68/0.86    inference(superposition,[],[f3957,f5991])).
% 3.68/0.86  fof(f3957,plain,(
% 3.68/0.86    k1_relat_1(k1_xboole_0) != k7_relset_1(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0),k1_xboole_0) | (~spl4_3 | ~spl4_5 | ~spl4_113 | ~spl4_135)),
% 3.68/0.86    inference(forward_demodulation,[],[f3956,f3948])).
% 3.68/0.86  fof(f3948,plain,(
% 3.68/0.86    k2_funct_1(k1_xboole_0) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0) | (~spl4_5 | ~spl4_113)),
% 3.68/0.86    inference(forward_demodulation,[],[f3771,f2785])).
% 3.68/0.86  fof(f3771,plain,(
% 3.68/0.86    k2_funct_1(k1_xboole_0) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(k1_xboole_0),k1_xboole_0) | ~spl4_5),
% 3.68/0.86    inference(superposition,[],[f923,f398])).
% 3.68/0.86  fof(f923,plain,(
% 3.68/0.86    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 3.68/0.86    inference(forward_demodulation,[],[f922,f106])).
% 3.68/0.86  fof(f922,plain,(
% 3.68/0.86    k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 3.68/0.86    inference(forward_demodulation,[],[f282,f909])).
% 3.68/0.86  fof(f282,plain,(
% 3.68/0.86    k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 3.68/0.86    inference(forward_demodulation,[],[f281,f107])).
% 3.68/0.86  fof(f281,plain,(
% 3.68/0.86    k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)),
% 3.68/0.86    inference(subsumption_resolution,[],[f280,f107])).
% 3.68/0.86  fof(f280,plain,(
% 3.68/0.86    u1_struct_0(sK1) != k2_struct_0(sK1) | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)),
% 3.68/0.86    inference(forward_demodulation,[],[f279,f64])).
% 3.68/0.86  fof(f279,plain,(
% 3.68/0.86    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)),
% 3.68/0.86    inference(subsumption_resolution,[],[f278,f60])).
% 3.68/0.86  fof(f278,plain,(
% 3.68/0.86    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) | ~v1_funct_1(sK2)),
% 3.68/0.86    inference(subsumption_resolution,[],[f277,f61])).
% 3.68/0.86  fof(f277,plain,(
% 3.68/0.86    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 3.68/0.86    inference(subsumption_resolution,[],[f273,f65])).
% 3.68/0.86  fof(f273,plain,(
% 3.68/0.86    ~v2_funct_1(sK2) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 3.68/0.86    inference(resolution,[],[f96,f62])).
% 3.68/0.86  fof(f96,plain,(
% 3.68/0.86    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.68/0.86    inference(cnf_transformation,[],[f45])).
% 3.68/0.86  fof(f45,plain,(
% 3.68/0.86    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.68/0.86    inference(flattening,[],[f44])).
% 3.68/0.86  fof(f44,plain,(
% 3.68/0.86    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.68/0.86    inference(ennf_transformation,[],[f17])).
% 3.68/0.86  fof(f17,axiom,(
% 3.68/0.86    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 3.68/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 3.68/0.86  fof(f3956,plain,(
% 3.68/0.86    k1_relat_1(k1_xboole_0) != k7_relset_1(k1_xboole_0,k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0),k1_xboole_0) | (~spl4_3 | ~spl4_5 | ~spl4_113 | ~spl4_135)),
% 3.68/0.86    inference(forward_demodulation,[],[f3955,f647])).
% 3.68/0.86  fof(f647,plain,(
% 3.68/0.86    ( ! [X0] : (k1_relat_1(k1_xboole_0) = k8_relset_1(X0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) )),
% 3.68/0.86    inference(superposition,[],[f185,f101])).
% 3.68/0.86  fof(f185,plain,(
% 3.68/0.86    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = k8_relset_1(X0,X1,k2_zfmisc_1(X0,X1),X1)) )),
% 3.68/0.86    inference(forward_demodulation,[],[f179,f132])).
% 3.68/0.86  fof(f132,plain,(
% 3.68/0.86    ( ! [X0,X1] : (k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1)) = k1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.68/0.86    inference(resolution,[],[f84,f104])).
% 3.68/0.86  fof(f104,plain,(
% 3.68/0.86    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 3.68/0.86    inference(forward_demodulation,[],[f68,f67])).
% 3.68/0.86  fof(f67,plain,(
% 3.68/0.86    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.68/0.86    inference(cnf_transformation,[],[f3])).
% 3.68/0.86  fof(f3,axiom,(
% 3.68/0.86    ! [X0] : k2_subset_1(X0) = X0),
% 3.68/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 3.68/0.86  fof(f68,plain,(
% 3.68/0.86    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.68/0.86    inference(cnf_transformation,[],[f4])).
% 3.68/0.86  fof(f4,axiom,(
% 3.68/0.86    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.68/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 3.68/0.86  fof(f179,plain,(
% 3.68/0.86    ( ! [X0,X1] : (k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1)) = k8_relset_1(X0,X1,k2_zfmisc_1(X0,X1),X1)) )),
% 3.68/0.86    inference(resolution,[],[f89,f104])).
% 3.68/0.86  fof(f89,plain,(
% 3.68/0.86    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)) )),
% 3.68/0.86    inference(cnf_transformation,[],[f39])).
% 3.68/0.86  fof(f3955,plain,(
% 3.68/0.86    k7_relset_1(k1_xboole_0,k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0),k1_xboole_0) != k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_3 | ~spl4_5 | ~spl4_113 | ~spl4_135)),
% 3.68/0.86    inference(forward_demodulation,[],[f3853,f2785])).
% 3.68/0.86  fof(f3853,plain,(
% 3.68/0.86    k8_relset_1(k2_struct_0(sK0),k2_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != k7_relset_1(k2_relat_1(k1_xboole_0),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(k1_xboole_0),k1_xboole_0),k1_xboole_0) | (~spl4_3 | ~spl4_5 | ~spl4_135)),
% 3.68/0.86    inference(forward_demodulation,[],[f3768,f3658])).
% 3.68/0.86  fof(f3658,plain,(
% 3.68/0.86    k1_xboole_0 = sK3 | (~spl4_3 | ~spl4_135)),
% 3.68/0.86    inference(forward_demodulation,[],[f3301,f3308])).
% 3.68/0.86  fof(f3308,plain,(
% 3.68/0.86    k1_xboole_0 = k2_relat_1(sK2) | ~spl4_3),
% 3.68/0.86    inference(global_subsumption,[],[f331])).
% 3.68/0.86  fof(f331,plain,(
% 3.68/0.86    k1_xboole_0 = k2_relat_1(sK2) | ~spl4_3),
% 3.68/0.86    inference(forward_demodulation,[],[f330,f225])).
% 3.68/0.86  fof(f225,plain,(
% 3.68/0.86    k1_xboole_0 = k2_struct_0(sK1) | ~spl4_3),
% 3.68/0.86    inference(avatar_component_clause,[],[f223])).
% 3.68/0.86  fof(f223,plain,(
% 3.68/0.86    spl4_3 <=> k1_xboole_0 = k2_struct_0(sK1)),
% 3.68/0.86    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 3.68/0.86  fof(f330,plain,(
% 3.68/0.86    k2_struct_0(sK1) = k2_relat_1(sK2)),
% 3.68/0.86    inference(forward_demodulation,[],[f329,f153])).
% 3.68/0.86  fof(f329,plain,(
% 3.68/0.86    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 3.68/0.86    inference(forward_demodulation,[],[f320,f107])).
% 3.68/0.86  fof(f320,plain,(
% 3.68/0.86    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 3.68/0.86    inference(superposition,[],[f64,f106])).
% 3.68/0.86  fof(f3301,plain,(
% 3.68/0.86    sK3 = k2_relat_1(sK2) | ~spl4_135),
% 3.68/0.86    inference(avatar_component_clause,[],[f3299])).
% 3.68/0.86  fof(f3299,plain,(
% 3.68/0.86    spl4_135 <=> sK3 = k2_relat_1(sK2)),
% 3.68/0.86    introduced(avatar_definition,[new_symbols(naming,[spl4_135])])).
% 3.68/0.86  fof(f3768,plain,(
% 3.68/0.86    k8_relset_1(k2_struct_0(sK0),k2_relat_1(k1_xboole_0),k1_xboole_0,sK3) != k7_relset_1(k2_relat_1(k1_xboole_0),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(k1_xboole_0),k1_xboole_0),sK3) | ~spl4_5),
% 3.68/0.86    inference(superposition,[],[f911,f398])).
% 3.68/0.86  fof(f911,plain,(
% 3.68/0.86    k8_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK3) != k7_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2),sK3)),
% 3.68/0.86    inference(forward_demodulation,[],[f910,f106])).
% 3.68/0.86  fof(f910,plain,(
% 3.68/0.86    k8_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2,sK3) != k7_relset_1(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2),sK3)),
% 3.68/0.86    inference(forward_demodulation,[],[f340,f909])).
% 3.68/0.86  fof(f340,plain,(
% 3.68/0.86    k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k7_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)),
% 3.68/0.86    inference(superposition,[],[f66,f107])).
% 3.68/0.86  fof(f66,plain,(
% 3.68/0.86    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)),
% 3.68/0.86    inference(cnf_transformation,[],[f52])).
% 3.68/0.86  fof(f5977,plain,(
% 3.68/0.86    ~spl4_5 | spl4_10 | ~spl4_113),
% 3.68/0.86    inference(avatar_contradiction_clause,[],[f5972])).
% 3.68/0.86  fof(f5972,plain,(
% 3.68/0.86    $false | (~spl4_5 | spl4_10 | ~spl4_113)),
% 3.68/0.86    inference(resolution,[],[f5777,f754])).
% 3.68/0.86  fof(f754,plain,(
% 3.68/0.86    ~r1_tarski(k1_xboole_0,k2_funct_1(sK2)) | spl4_10),
% 3.68/0.86    inference(avatar_component_clause,[],[f752])).
% 3.68/0.86  fof(f752,plain,(
% 3.68/0.86    spl4_10 <=> r1_tarski(k1_xboole_0,k2_funct_1(sK2))),
% 3.68/0.86    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 3.68/0.86  fof(f5777,plain,(
% 3.68/0.86    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | (~spl4_5 | ~spl4_113)),
% 3.68/0.86    inference(resolution,[],[f5735,f78])).
% 3.68/0.86  fof(f78,plain,(
% 3.68/0.86    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 3.68/0.86    inference(cnf_transformation,[],[f55])).
% 3.68/0.86  fof(f55,plain,(
% 3.68/0.86    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.68/0.86    inference(nnf_transformation,[],[f5])).
% 3.68/0.86  fof(f5,axiom,(
% 3.68/0.86    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.68/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 3.68/0.86  fof(f3857,plain,(
% 3.68/0.86    ~spl4_3 | ~spl4_5 | spl4_112 | ~spl4_135),
% 3.68/0.86    inference(avatar_contradiction_clause,[],[f3856])).
% 3.68/0.86  fof(f3856,plain,(
% 3.68/0.86    $false | (~spl4_3 | ~spl4_5 | spl4_112 | ~spl4_135)),
% 3.68/0.86    inference(subsumption_resolution,[],[f3855,f2781])).
% 3.68/0.86  fof(f2781,plain,(
% 3.68/0.86    ~r1_tarski(k1_xboole_0,k2_relat_1(k1_xboole_0)) | spl4_112),
% 3.68/0.86    inference(avatar_component_clause,[],[f2779])).
% 3.68/0.86  fof(f2779,plain,(
% 3.68/0.86    spl4_112 <=> r1_tarski(k1_xboole_0,k2_relat_1(k1_xboole_0))),
% 3.68/0.86    introduced(avatar_definition,[new_symbols(naming,[spl4_112])])).
% 3.68/0.86  fof(f3855,plain,(
% 3.68/0.86    r1_tarski(k1_xboole_0,k2_relat_1(k1_xboole_0)) | (~spl4_3 | ~spl4_5 | ~spl4_135)),
% 3.68/0.86    inference(forward_demodulation,[],[f3776,f3658])).
% 3.68/0.86  fof(f3776,plain,(
% 3.68/0.86    r1_tarski(sK3,k2_relat_1(k1_xboole_0)) | ~spl4_5),
% 3.68/0.86    inference(superposition,[],[f1178,f398])).
% 3.68/0.86  fof(f1178,plain,(
% 3.68/0.86    r1_tarski(sK3,k2_relat_1(sK2))),
% 3.68/0.86    inference(superposition,[],[f111,f909])).
% 3.68/0.86  fof(f111,plain,(
% 3.68/0.86    r1_tarski(sK3,k2_struct_0(sK1))),
% 3.68/0.86    inference(forward_demodulation,[],[f108,f107])).
% 3.68/0.86  fof(f108,plain,(
% 3.68/0.86    r1_tarski(sK3,u1_struct_0(sK1))),
% 3.68/0.86    inference(resolution,[],[f78,f63])).
% 3.68/0.86  fof(f63,plain,(
% 3.68/0.86    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 3.68/0.86    inference(cnf_transformation,[],[f52])).
% 3.68/0.86  fof(f3657,plain,(
% 3.68/0.86    ~spl4_1 | ~spl4_3 | spl4_134),
% 3.68/0.86    inference(avatar_contradiction_clause,[],[f3656])).
% 3.68/0.86  fof(f3656,plain,(
% 3.68/0.86    $false | (~spl4_1 | ~spl4_3 | spl4_134)),
% 3.68/0.86    inference(global_subsumption,[],[f3628,f3638])).
% 3.68/0.86  fof(f3638,plain,(
% 3.68/0.86    ~r1_tarski(k1_xboole_0,sK3) | (~spl4_3 | spl4_134)),
% 3.68/0.86    inference(forward_demodulation,[],[f3297,f3308])).
% 3.68/0.86  fof(f3297,plain,(
% 3.68/0.86    ~r1_tarski(k2_relat_1(sK2),sK3) | spl4_134),
% 3.68/0.86    inference(avatar_component_clause,[],[f3295])).
% 3.68/0.86  fof(f3295,plain,(
% 3.68/0.86    spl4_134 <=> r1_tarski(k2_relat_1(sK2),sK3)),
% 3.68/0.86    introduced(avatar_definition,[new_symbols(naming,[spl4_134])])).
% 3.68/0.86  fof(f3628,plain,(
% 3.68/0.86    r1_tarski(k1_xboole_0,sK3) | (~spl4_1 | ~spl4_3)),
% 3.68/0.86    inference(forward_demodulation,[],[f3627,f3308])).
% 3.68/0.86  fof(f3627,plain,(
% 3.68/0.86    r1_tarski(k2_relat_1(sK2),sK3) | ~spl4_1),
% 3.68/0.86    inference(forward_demodulation,[],[f141,f909])).
% 3.68/0.86  fof(f141,plain,(
% 3.68/0.86    r1_tarski(k2_struct_0(sK1),sK3) | ~spl4_1),
% 3.68/0.86    inference(avatar_component_clause,[],[f140])).
% 3.68/0.86  fof(f140,plain,(
% 3.68/0.86    spl4_1 <=> r1_tarski(k2_struct_0(sK1),sK3)),
% 3.68/0.86    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 3.68/0.86  fof(f3302,plain,(
% 3.68/0.86    ~spl4_134 | spl4_135),
% 3.68/0.86    inference(avatar_split_clause,[],[f1223,f3299,f3295])).
% 3.68/0.86  fof(f1223,plain,(
% 3.68/0.86    sK3 = k2_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),sK3)),
% 3.68/0.86    inference(resolution,[],[f1178,f77])).
% 3.68/0.86  fof(f77,plain,(
% 3.68/0.86    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.68/0.86    inference(cnf_transformation,[],[f54])).
% 3.68/0.86  fof(f54,plain,(
% 3.68/0.86    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.68/0.86    inference(flattening,[],[f53])).
% 3.68/0.86  fof(f53,plain,(
% 3.68/0.86    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.68/0.86    inference(nnf_transformation,[],[f1])).
% 3.68/0.86  fof(f1,axiom,(
% 3.68/0.86    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.68/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.68/0.86  fof(f3293,plain,(
% 3.68/0.86    ~spl4_4 | ~spl4_14),
% 3.68/0.86    inference(avatar_contradiction_clause,[],[f3292])).
% 3.68/0.86  fof(f3292,plain,(
% 3.68/0.86    $false | (~spl4_4 | ~spl4_14)),
% 3.68/0.86    inference(subsumption_resolution,[],[f3291,f1012])).
% 3.68/0.86  fof(f1012,plain,(
% 3.68/0.86    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl4_4),
% 3.68/0.86    inference(forward_demodulation,[],[f1011,f130])).
% 3.68/0.86  fof(f130,plain,(
% 3.68/0.86    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 3.68/0.86    inference(subsumption_resolution,[],[f129,f115])).
% 3.68/0.86  fof(f129,plain,(
% 3.68/0.86    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 3.68/0.86    inference(subsumption_resolution,[],[f128,f60])).
% 3.68/0.86  fof(f128,plain,(
% 3.68/0.86    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 3.68/0.86    inference(resolution,[],[f74,f65])).
% 3.68/0.86  fof(f74,plain,(
% 3.68/0.86    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.68/0.86    inference(cnf_transformation,[],[f33])).
% 3.68/0.86  fof(f1011,plain,(
% 3.68/0.86    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl4_4),
% 3.68/0.86    inference(forward_demodulation,[],[f994,f229])).
% 3.68/0.86  fof(f229,plain,(
% 3.68/0.86    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl4_4),
% 3.68/0.86    inference(avatar_component_clause,[],[f227])).
% 3.68/0.86  fof(f227,plain,(
% 3.68/0.86    spl4_4 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 3.68/0.86    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 3.68/0.86  fof(f994,plain,(
% 3.68/0.86    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 3.68/0.86    inference(resolution,[],[f924,f85])).
% 3.68/0.86  fof(f3291,plain,(
% 3.68/0.86    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl4_4 | ~spl4_14)),
% 3.68/0.86    inference(forward_demodulation,[],[f3290,f982])).
% 3.68/0.86  fof(f982,plain,(
% 3.68/0.86    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl4_4),
% 3.68/0.86    inference(superposition,[],[f923,f229])).
% 3.68/0.86  fof(f3290,plain,(
% 3.68/0.86    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | (~spl4_4 | ~spl4_14)),
% 3.68/0.86    inference(subsumption_resolution,[],[f3289,f2412])).
% 3.68/0.86  fof(f2412,plain,(
% 3.68/0.86    k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK3) != k7_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2),sK3) | ~spl4_4),
% 3.68/0.86    inference(forward_demodulation,[],[f2410,f982])).
% 3.68/0.86  fof(f2410,plain,(
% 3.68/0.86    k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK3) != k7_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),sK3) | ~spl4_4),
% 3.68/0.86    inference(superposition,[],[f911,f229])).
% 3.68/0.86  fof(f3289,plain,(
% 3.68/0.86    k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK3) = k7_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2),sK3) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | (~spl4_4 | ~spl4_14)),
% 3.68/0.86    inference(forward_demodulation,[],[f3288,f1091])).
% 3.68/0.86  fof(f1091,plain,(
% 3.68/0.86    sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl4_4 | ~spl4_14)),
% 3.68/0.86    inference(forward_demodulation,[],[f1090,f122])).
% 3.68/0.86  fof(f122,plain,(
% 3.68/0.86    sK2 = k2_funct_1(k2_funct_1(sK2))),
% 3.68/0.86    inference(subsumption_resolution,[],[f121,f115])).
% 3.68/0.86  fof(f121,plain,(
% 3.68/0.86    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 3.68/0.86    inference(subsumption_resolution,[],[f120,f60])).
% 3.68/0.86  fof(f120,plain,(
% 3.68/0.86    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 3.68/0.86    inference(resolution,[],[f72,f65])).
% 3.68/0.86  fof(f72,plain,(
% 3.68/0.86    ( ! [X0] : (~v2_funct_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.68/0.86    inference(cnf_transformation,[],[f31])).
% 3.68/0.86  fof(f31,plain,(
% 3.68/0.86    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.68/0.86    inference(flattening,[],[f30])).
% 3.68/0.86  fof(f30,plain,(
% 3.68/0.86    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.68/0.86    inference(ennf_transformation,[],[f7])).
% 3.68/0.86  fof(f7,axiom,(
% 3.68/0.86    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 3.68/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
% 3.68/0.86  fof(f1090,plain,(
% 3.68/0.86    k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl4_4 | ~spl4_14)),
% 3.68/0.86    inference(forward_demodulation,[],[f1089,f229])).
% 3.68/0.86  fof(f1089,plain,(
% 3.68/0.86    k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | ~spl4_14),
% 3.68/0.86    inference(forward_demodulation,[],[f1088,f923])).
% 3.68/0.86  fof(f1088,plain,(
% 3.68/0.86    k2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | ~spl4_14),
% 3.68/0.86    inference(forward_demodulation,[],[f872,f909])).
% 3.68/0.86  fof(f872,plain,(
% 3.68/0.86    k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | ~spl4_14),
% 3.68/0.86    inference(avatar_component_clause,[],[f870])).
% 3.68/0.86  fof(f870,plain,(
% 3.68/0.86    spl4_14 <=> k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 3.68/0.86    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 3.68/0.86  fof(f3288,plain,(
% 3.68/0.86    k7_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2),sK3) = k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK3) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | ~spl4_4),
% 3.68/0.86    inference(forward_demodulation,[],[f3287,f982])).
% 3.68/0.86  fof(f3287,plain,(
% 3.68/0.86    k7_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),sK3) = k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK3) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | ~spl4_4),
% 3.68/0.86    inference(subsumption_resolution,[],[f3286,f969])).
% 3.68/0.86  fof(f969,plain,(
% 3.68/0.86    v1_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | ~spl4_4),
% 3.68/0.86    inference(forward_demodulation,[],[f961,f909])).
% 3.68/0.86  fof(f961,plain,(
% 3.68/0.86    v1_funct_1(k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)) | ~spl4_4),
% 3.68/0.86    inference(superposition,[],[f193,f229])).
% 3.68/0.86  fof(f193,plain,(
% 3.68/0.86    v1_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 3.68/0.86    inference(forward_demodulation,[],[f192,f106])).
% 3.68/0.86  fof(f192,plain,(
% 3.68/0.86    v1_funct_1(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 3.68/0.86    inference(forward_demodulation,[],[f191,f107])).
% 3.68/0.86  fof(f191,plain,(
% 3.68/0.86    v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 3.68/0.86    inference(subsumption_resolution,[],[f190,f60])).
% 3.68/0.86  fof(f190,plain,(
% 3.68/0.86    v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_1(sK2)),
% 3.68/0.86    inference(subsumption_resolution,[],[f186,f61])).
% 3.68/0.86  fof(f186,plain,(
% 3.68/0.86    v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 3.68/0.86    inference(resolution,[],[f90,f62])).
% 3.68/0.86  fof(f90,plain,(
% 3.68/0.86    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k2_tops_2(X0,X1,X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.68/0.86    inference(cnf_transformation,[],[f41])).
% 3.68/0.86  fof(f41,plain,(
% 3.68/0.86    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.68/0.86    inference(flattening,[],[f40])).
% 3.68/0.86  fof(f40,plain,(
% 3.68/0.86    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.68/0.86    inference(ennf_transformation,[],[f18])).
% 3.68/0.86  fof(f18,axiom,(
% 3.68/0.86    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 3.68/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).
% 3.68/0.86  fof(f3286,plain,(
% 3.68/0.86    k7_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),sK3) = k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK3) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | ~v1_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | ~spl4_4),
% 3.68/0.86    inference(subsumption_resolution,[],[f3285,f975])).
% 3.68/0.86  fof(f975,plain,(
% 3.68/0.86    v2_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | ~spl4_4),
% 3.68/0.86    inference(superposition,[],[f921,f229])).
% 3.68/0.86  fof(f921,plain,(
% 3.68/0.86    v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))),
% 3.68/0.86    inference(forward_demodulation,[],[f920,f106])).
% 3.68/0.86  fof(f920,plain,(
% 3.68/0.86    v2_funct_1(k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2))),
% 3.68/0.86    inference(forward_demodulation,[],[f294,f909])).
% 3.68/0.86  fof(f294,plain,(
% 3.68/0.86    v2_funct_1(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 3.68/0.86    inference(forward_demodulation,[],[f293,f107])).
% 3.68/0.86  fof(f293,plain,(
% 3.68/0.86    v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 3.68/0.86    inference(subsumption_resolution,[],[f292,f58])).
% 3.68/0.86  fof(f292,plain,(
% 3.68/0.86    v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~l1_struct_0(sK0)),
% 3.68/0.86    inference(subsumption_resolution,[],[f291,f59])).
% 3.68/0.86  fof(f291,plain,(
% 3.68/0.86    v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~l1_struct_0(sK1) | ~l1_struct_0(sK0)),
% 3.68/0.86    inference(subsumption_resolution,[],[f290,f60])).
% 3.68/0.86  fof(f290,plain,(
% 3.68/0.86    v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_1(sK2) | ~l1_struct_0(sK1) | ~l1_struct_0(sK0)),
% 3.68/0.86    inference(subsumption_resolution,[],[f289,f61])).
% 3.68/0.86  fof(f289,plain,(
% 3.68/0.86    v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_struct_0(sK1) | ~l1_struct_0(sK0)),
% 3.68/0.86    inference(subsumption_resolution,[],[f288,f64])).
% 3.68/0.86  fof(f288,plain,(
% 3.68/0.86    k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_struct_0(sK1) | ~l1_struct_0(sK0)),
% 3.68/0.86    inference(subsumption_resolution,[],[f286,f65])).
% 3.68/0.86  fof(f286,plain,(
% 3.68/0.86    ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_struct_0(sK1) | ~l1_struct_0(sK0)),
% 3.68/0.86    inference(resolution,[],[f70,f62])).
% 3.68/0.86  fof(f70,plain,(
% 3.68/0.86    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.68/0.86    inference(cnf_transformation,[],[f27])).
% 3.68/0.86  fof(f27,plain,(
% 3.68/0.86    ! [X0] : (! [X1] : (! [X2] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 3.68/0.86    inference(flattening,[],[f26])).
% 3.68/0.86  fof(f26,plain,(
% 3.68/0.86    ! [X0] : (! [X1] : (! [X2] : ((v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 3.68/0.86    inference(ennf_transformation,[],[f19])).
% 3.68/0.86  fof(f19,axiom,(
% 3.68/0.86    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 3.68/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_tops_2)).
% 3.68/0.86  fof(f3285,plain,(
% 3.68/0.86    k7_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),sK3) = k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK3) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | ~v2_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | ~v1_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | ~spl4_4),
% 3.68/0.86    inference(subsumption_resolution,[],[f3271,f970])).
% 3.68/0.86  fof(f970,plain,(
% 3.68/0.86    v1_funct_2(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~spl4_4),
% 3.68/0.86    inference(forward_demodulation,[],[f962,f909])).
% 3.68/0.86  fof(f962,plain,(
% 3.68/0.86    v1_funct_2(k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2),k2_struct_0(sK1),k1_relat_1(sK2)) | ~spl4_4),
% 3.68/0.86    inference(superposition,[],[f201,f229])).
% 3.68/0.86  fof(f201,plain,(
% 3.68/0.86    v1_funct_2(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k2_struct_0(sK1),k2_struct_0(sK0))),
% 3.68/0.86    inference(forward_demodulation,[],[f200,f107])).
% 3.68/0.86  fof(f200,plain,(
% 3.68/0.86    v1_funct_2(k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),k2_struct_0(sK0))),
% 3.68/0.86    inference(forward_demodulation,[],[f199,f106])).
% 3.68/0.86  fof(f199,plain,(
% 3.68/0.86    v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))),
% 3.68/0.86    inference(subsumption_resolution,[],[f198,f60])).
% 3.68/0.86  fof(f198,plain,(
% 3.68/0.86    v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2)),
% 3.68/0.86    inference(subsumption_resolution,[],[f194,f61])).
% 3.68/0.86  fof(f194,plain,(
% 3.68/0.86    v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 3.68/0.86    inference(resolution,[],[f91,f62])).
% 3.68/0.86  fof(f91,plain,(
% 3.68/0.86    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.68/0.86    inference(cnf_transformation,[],[f41])).
% 3.68/0.86  fof(f3271,plain,(
% 3.68/0.86    k7_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),sK3) = k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK3) | ~v1_funct_2(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | ~v2_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | ~v1_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | ~spl4_4),
% 3.68/0.86    inference(resolution,[],[f1117,f971])).
% 3.68/0.86  fof(f971,plain,(
% 3.68/0.86    m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~spl4_4),
% 3.68/0.86    inference(forward_demodulation,[],[f963,f909])).
% 3.68/0.86  fof(f963,plain,(
% 3.68/0.86    m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2)))) | ~spl4_4),
% 3.68/0.86    inference(superposition,[],[f209,f229])).
% 3.68/0.86  fof(f209,plain,(
% 3.68/0.86    m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 3.68/0.86    inference(forward_demodulation,[],[f208,f107])).
% 3.68/0.86  fof(f208,plain,(
% 3.68/0.86    m1_subset_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK0))))),
% 3.68/0.86    inference(forward_demodulation,[],[f207,f106])).
% 3.68/0.86  fof(f207,plain,(
% 3.68/0.86    m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 3.68/0.86    inference(subsumption_resolution,[],[f206,f60])).
% 3.68/0.86  fof(f206,plain,(
% 3.68/0.86    m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(sK2)),
% 3.68/0.86    inference(subsumption_resolution,[],[f202,f61])).
% 3.68/0.86  fof(f202,plain,(
% 3.68/0.86    m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 3.68/0.86    inference(resolution,[],[f92,f62])).
% 3.68/0.86  fof(f92,plain,(
% 3.68/0.86    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.68/0.86    inference(cnf_transformation,[],[f41])).
% 3.68/0.86  fof(f1117,plain,(
% 3.68/0.86    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | k7_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),X0,sK3) = k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),X0),sK3) | ~v1_funct_2(X0,k2_relat_1(sK2),k1_relat_1(sK2)) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0)) ) | ~spl4_4),
% 3.68/0.86    inference(forward_demodulation,[],[f1116,f229])).
% 3.68/0.86  fof(f1116,plain,(
% 3.68/0.86    ( ! [X0] : (k7_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),X0,sK3) = k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),X0),sK3) | ~v1_funct_2(X0,k2_relat_1(sK2),k1_relat_1(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0)) ) | ~spl4_4),
% 3.68/0.86    inference(forward_demodulation,[],[f1115,f229])).
% 3.68/0.86  fof(f1115,plain,(
% 3.68/0.86    ( ! [X0] : (~v1_funct_2(X0,k2_relat_1(sK2),k1_relat_1(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | k7_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),X0,sK3) = k8_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),X0),sK3) | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0)) ) | ~spl4_4),
% 3.68/0.86    inference(forward_demodulation,[],[f1114,f229])).
% 3.68/0.86  fof(f1114,plain,(
% 3.68/0.86    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_2(X0,k2_relat_1(sK2),k2_struct_0(sK0)) | k7_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),X0,sK3) = k8_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),X0),sK3) | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0)) ) | ~spl4_4),
% 3.68/0.86    inference(forward_demodulation,[],[f1113,f229])).
% 3.68/0.86  fof(f1113,plain,(
% 3.68/0.86    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | ~v1_funct_2(X0,k2_relat_1(sK2),k2_struct_0(sK0)) | k7_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),X0,sK3) = k8_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),X0),sK3) | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0)) )),
% 3.68/0.86    inference(subsumption_resolution,[],[f1108,f58])).
% 3.68/0.86  fof(f1108,plain,(
% 3.68/0.86    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | ~v1_funct_2(X0,k2_relat_1(sK2),k2_struct_0(sK0)) | k7_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),X0,sK3) = k8_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),X0),sK3) | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~l1_struct_0(sK0)) )),
% 3.68/0.86    inference(superposition,[],[f919,f106])).
% 3.68/0.86  fof(f919,plain,(
% 3.68/0.86    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),u1_struct_0(X1)))) | ~v1_funct_2(X0,k2_relat_1(sK2),u1_struct_0(X1)) | k7_relset_1(k2_relat_1(sK2),u1_struct_0(X1),X0,sK3) = k8_relset_1(u1_struct_0(X1),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),u1_struct_0(X1),X0),sK3) | k2_struct_0(X1) != k2_relset_1(k2_relat_1(sK2),u1_struct_0(X1),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~l1_struct_0(X1)) )),
% 3.68/0.86    inference(forward_demodulation,[],[f918,f909])).
% 3.68/0.86  fof(f918,plain,(
% 3.68/0.86    ( ! [X0,X1] : (~v1_funct_2(X0,k2_struct_0(sK1),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),u1_struct_0(X1)))) | k7_relset_1(k2_relat_1(sK2),u1_struct_0(X1),X0,sK3) = k8_relset_1(u1_struct_0(X1),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),u1_struct_0(X1),X0),sK3) | k2_struct_0(X1) != k2_relset_1(k2_relat_1(sK2),u1_struct_0(X1),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~l1_struct_0(X1)) )),
% 3.68/0.86    inference(forward_demodulation,[],[f917,f107])).
% 3.68/0.86  fof(f917,plain,(
% 3.68/0.86    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),u1_struct_0(X1)))) | k7_relset_1(k2_relat_1(sK2),u1_struct_0(X1),X0,sK3) = k8_relset_1(u1_struct_0(X1),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),u1_struct_0(X1),X0),sK3) | k2_struct_0(X1) != k2_relset_1(k2_relat_1(sK2),u1_struct_0(X1),X0) | ~v2_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_struct_0(X1)) )),
% 3.68/0.86    inference(forward_demodulation,[],[f916,f909])).
% 3.68/0.86  fof(f916,plain,(
% 3.68/0.86    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X1)))) | k7_relset_1(k2_relat_1(sK2),u1_struct_0(X1),X0,sK3) = k8_relset_1(u1_struct_0(X1),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),u1_struct_0(X1),X0),sK3) | k2_struct_0(X1) != k2_relset_1(k2_relat_1(sK2),u1_struct_0(X1),X0) | ~v2_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_struct_0(X1)) )),
% 3.68/0.86    inference(forward_demodulation,[],[f915,f107])).
% 3.68/0.86  fof(f915,plain,(
% 3.68/0.86    ( ! [X0,X1] : (k7_relset_1(k2_relat_1(sK2),u1_struct_0(X1),X0,sK3) = k8_relset_1(u1_struct_0(X1),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),u1_struct_0(X1),X0),sK3) | k2_struct_0(X1) != k2_relset_1(k2_relat_1(sK2),u1_struct_0(X1),X0) | ~v2_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_struct_0(X1)) )),
% 3.68/0.86    inference(forward_demodulation,[],[f914,f909])).
% 3.68/0.86  fof(f914,plain,(
% 3.68/0.86    ( ! [X0,X1] : (k7_relset_1(k2_struct_0(sK1),u1_struct_0(X1),X0,sK3) = k8_relset_1(u1_struct_0(X1),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(X1),X0),sK3) | k2_struct_0(X1) != k2_relset_1(k2_relat_1(sK2),u1_struct_0(X1),X0) | ~v2_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_struct_0(X1)) )),
% 3.68/0.86    inference(forward_demodulation,[],[f913,f107])).
% 3.68/0.86  fof(f913,plain,(
% 3.68/0.86    ( ! [X0,X1] : (k2_struct_0(X1) != k2_relset_1(k2_relat_1(sK2),u1_struct_0(X1),X0) | ~v2_funct_1(X0) | k7_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X0,sK3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X0),sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_struct_0(X1)) )),
% 3.68/0.86    inference(forward_demodulation,[],[f302,f909])).
% 3.68/0.86  fof(f302,plain,(
% 3.68/0.86    ( ! [X0,X1] : (k2_struct_0(X1) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(X1),X0) | ~v2_funct_1(X0) | k7_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X0,sK3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X0),sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_struct_0(X1)) )),
% 3.68/0.86    inference(forward_demodulation,[],[f301,f107])).
% 3.68/0.86  fof(f301,plain,(
% 3.68/0.86    ( ! [X0,X1] : (~v2_funct_1(X0) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X0) | k7_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X0,sK3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X0),sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_struct_0(X1)) )),
% 3.68/0.86    inference(subsumption_resolution,[],[f299,f59])).
% 3.68/0.86  fof(f299,plain,(
% 3.68/0.86    ( ! [X0,X1] : (~v2_funct_1(X0) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X0) | k7_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X0,sK3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X0),sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_struct_0(X1) | ~l1_struct_0(sK1)) )),
% 3.68/0.86    inference(resolution,[],[f71,f63])).
% 3.68/0.86  fof(f71,plain,(
% 3.68/0.86    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.68/0.86    inference(cnf_transformation,[],[f29])).
% 3.68/0.86  fof(f29,plain,(
% 3.68/0.86    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 3.68/0.86    inference(flattening,[],[f28])).
% 3.68/0.86  fof(f28,plain,(
% 3.68/0.86    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 3.68/0.86    inference(ennf_transformation,[],[f20])).
% 3.68/0.86  fof(f20,axiom,(
% 3.68/0.86    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3))))))),
% 3.68/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tops_2)).
% 3.68/0.86  fof(f2786,plain,(
% 3.68/0.86    ~spl4_112 | spl4_113),
% 3.68/0.86    inference(avatar_split_clause,[],[f2776,f2783,f2779])).
% 3.68/0.86  fof(f2776,plain,(
% 3.68/0.86    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0,k2_relat_1(k1_xboole_0))),
% 3.68/0.86    inference(resolution,[],[f1509,f77])).
% 3.68/0.86  fof(f1509,plain,(
% 3.68/0.86    r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0)),
% 3.68/0.86    inference(resolution,[],[f555,f78])).
% 3.68/0.86  fof(f555,plain,(
% 3.68/0.86    m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 3.68/0.86    inference(superposition,[],[f169,f101])).
% 3.68/0.86  fof(f169,plain,(
% 3.68/0.86    ( ! [X0,X1] : (m1_subset_1(k2_relat_1(k2_zfmisc_1(X0,X1)),k1_zfmisc_1(X1))) )),
% 3.68/0.86    inference(forward_demodulation,[],[f163,f149])).
% 3.68/0.86  fof(f149,plain,(
% 3.68/0.86    ( ! [X0,X1] : (k2_relset_1(X0,X1,k2_zfmisc_1(X0,X1)) = k2_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.68/0.86    inference(resolution,[],[f85,f104])).
% 3.68/0.86  fof(f163,plain,(
% 3.68/0.86    ( ! [X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,k2_zfmisc_1(X0,X1)),k1_zfmisc_1(X1))) )),
% 3.68/0.86    inference(resolution,[],[f87,f104])).
% 3.68/0.86  fof(f87,plain,(
% 3.68/0.86    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))) )),
% 3.68/0.86    inference(cnf_transformation,[],[f38])).
% 3.68/0.86  fof(f38,plain,(
% 3.68/0.86    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.68/0.86    inference(ennf_transformation,[],[f10])).
% 3.68/0.86  fof(f10,axiom,(
% 3.68/0.86    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 3.68/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 3.68/0.86  fof(f1014,plain,(
% 3.68/0.86    ~spl4_4 | spl4_15),
% 3.68/0.86    inference(avatar_contradiction_clause,[],[f1013])).
% 3.68/0.86  fof(f1013,plain,(
% 3.68/0.86    $false | (~spl4_4 | spl4_15)),
% 3.68/0.86    inference(subsumption_resolution,[],[f1012,f944])).
% 3.68/0.86  fof(f944,plain,(
% 3.68/0.86    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl4_4 | spl4_15)),
% 3.68/0.86    inference(forward_demodulation,[],[f943,f229])).
% 3.68/0.86  fof(f943,plain,(
% 3.68/0.86    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | spl4_15),
% 3.68/0.86    inference(forward_demodulation,[],[f942,f923])).
% 3.68/0.86  fof(f942,plain,(
% 3.68/0.86    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | spl4_15),
% 3.68/0.86    inference(forward_demodulation,[],[f876,f909])).
% 3.68/0.86  fof(f876,plain,(
% 3.68/0.86    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | spl4_15),
% 3.68/0.86    inference(avatar_component_clause,[],[f874])).
% 3.68/0.86  fof(f874,plain,(
% 3.68/0.86    spl4_15 <=> k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 3.68/0.86    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 3.68/0.86  fof(f941,plain,(
% 3.68/0.86    spl4_16),
% 3.68/0.86    inference(avatar_contradiction_clause,[],[f940])).
% 3.68/0.86  fof(f940,plain,(
% 3.68/0.86    $false | spl4_16),
% 3.68/0.86    inference(subsumption_resolution,[],[f939,f921])).
% 3.68/0.86  fof(f939,plain,(
% 3.68/0.86    ~v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | spl4_16),
% 3.68/0.86    inference(forward_demodulation,[],[f880,f909])).
% 3.68/0.86  fof(f880,plain,(
% 3.68/0.86    ~v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | spl4_16),
% 3.68/0.86    inference(avatar_component_clause,[],[f878])).
% 3.68/0.86  fof(f878,plain,(
% 3.68/0.86    spl4_16 <=> v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 3.68/0.86    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 3.68/0.86  fof(f881,plain,(
% 3.68/0.86    spl4_14 | ~spl4_15 | ~spl4_16),
% 3.68/0.86    inference(avatar_split_clause,[],[f486,f878,f874,f870])).
% 3.68/0.86  fof(f486,plain,(
% 3.68/0.86    ~v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 3.68/0.86    inference(subsumption_resolution,[],[f485,f193])).
% 3.68/0.86  fof(f485,plain,(
% 3.68/0.86    ~v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | ~v1_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 3.68/0.86    inference(subsumption_resolution,[],[f432,f201])).
% 3.68/0.86  fof(f432,plain,(
% 3.68/0.86    ~v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | ~v1_funct_2(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~v1_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 3.68/0.86    inference(resolution,[],[f209,f96])).
% 3.68/0.86  fof(f859,plain,(
% 3.68/0.86    spl4_1 | ~spl4_3),
% 3.68/0.86    inference(avatar_contradiction_clause,[],[f854])).
% 3.68/0.86  fof(f854,plain,(
% 3.68/0.86    $false | (spl4_1 | ~spl4_3)),
% 3.68/0.86    inference(resolution,[],[f772,f232])).
% 3.68/0.86  fof(f232,plain,(
% 3.68/0.86    ~r1_tarski(k1_xboole_0,sK3) | (spl4_1 | ~spl4_3)),
% 3.68/0.86    inference(superposition,[],[f142,f225])).
% 3.68/0.86  fof(f142,plain,(
% 3.68/0.86    ~r1_tarski(k2_struct_0(sK1),sK3) | spl4_1),
% 3.68/0.86    inference(avatar_component_clause,[],[f140])).
% 3.68/0.86  fof(f772,plain,(
% 3.68/0.86    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl4_3),
% 3.68/0.86    inference(resolution,[],[f611,f78])).
% 3.68/0.86  fof(f611,plain,(
% 3.68/0.86    ( ! [X3] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))) ) | ~spl4_3),
% 3.68/0.86    inference(forward_demodulation,[],[f606,f578])).
% 3.68/0.86  fof(f578,plain,(
% 3.68/0.86    ( ! [X3] : (k1_xboole_0 = k1_relset_1(X3,k1_xboole_0,k2_funct_1(sK2))) ) | ~spl4_3),
% 3.68/0.86    inference(forward_demodulation,[],[f577,f331])).
% 3.68/0.86  fof(f577,plain,(
% 3.68/0.86    ( ! [X3] : (k2_relat_1(sK2) = k1_relset_1(X3,k1_xboole_0,k2_funct_1(sK2))) ) | ~spl4_3),
% 3.68/0.86    inference(forward_demodulation,[],[f574,f127])).
% 3.68/0.86  fof(f574,plain,(
% 3.68/0.86    ( ! [X3] : (k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(X3,k1_xboole_0,k2_funct_1(sK2))) ) | ~spl4_3),
% 3.68/0.86    inference(resolution,[],[f133,f269])).
% 3.68/0.86  fof(f269,plain,(
% 3.68/0.86    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | ~spl4_3),
% 3.68/0.86    inference(forward_demodulation,[],[f268,f102])).
% 3.68/0.86  fof(f268,plain,(
% 3.68/0.86    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | ~spl4_3),
% 3.68/0.86    inference(forward_demodulation,[],[f267,f225])).
% 3.68/0.86  fof(f606,plain,(
% 3.68/0.86    ( ! [X3] : (m1_subset_1(k1_relset_1(X3,k1_xboole_0,k2_funct_1(sK2)),k1_zfmisc_1(X3))) ) | ~spl4_3),
% 3.68/0.86    inference(resolution,[],[f156,f269])).
% 3.68/0.86  fof(f858,plain,(
% 3.68/0.86    ~spl4_3 | spl4_6),
% 3.68/0.86    inference(avatar_contradiction_clause,[],[f855])).
% 3.68/0.86  fof(f855,plain,(
% 3.68/0.86    $false | (~spl4_3 | spl4_6)),
% 3.68/0.86    inference(resolution,[],[f772,f402])).
% 3.68/0.86  fof(f402,plain,(
% 3.68/0.86    ~r1_tarski(k1_xboole_0,sK2) | spl4_6),
% 3.68/0.86    inference(avatar_component_clause,[],[f400])).
% 3.68/0.86  fof(f400,plain,(
% 3.68/0.86    spl4_6 <=> r1_tarski(k1_xboole_0,sK2)),
% 3.68/0.86    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 3.68/0.86  fof(f759,plain,(
% 3.68/0.86    ~spl4_10 | spl4_11 | ~spl4_3),
% 3.68/0.86    inference(avatar_split_clause,[],[f749,f223,f756,f752])).
% 3.68/0.86  fof(f749,plain,(
% 3.68/0.86    k1_xboole_0 = k2_funct_1(sK2) | ~r1_tarski(k1_xboole_0,k2_funct_1(sK2)) | ~spl4_3),
% 3.68/0.86    inference(resolution,[],[f378,f77])).
% 3.68/0.86  fof(f378,plain,(
% 3.68/0.86    r1_tarski(k2_funct_1(sK2),k1_xboole_0) | ~spl4_3),
% 3.68/0.86    inference(resolution,[],[f269,f78])).
% 3.68/0.86  fof(f403,plain,(
% 3.68/0.86    spl4_5 | ~spl4_6 | ~spl4_3),
% 3.68/0.86    inference(avatar_split_clause,[],[f394,f223,f400,f396])).
% 3.68/0.86  fof(f394,plain,(
% 3.68/0.86    ~r1_tarski(k1_xboole_0,sK2) | k1_xboole_0 = sK2 | ~spl4_3),
% 3.68/0.86    inference(forward_demodulation,[],[f393,f101])).
% 3.68/0.86  fof(f393,plain,(
% 3.68/0.86    ~r1_tarski(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0),sK2) | k1_xboole_0 = sK2 | ~spl4_3),
% 3.68/0.86    inference(forward_demodulation,[],[f392,f225])).
% 3.68/0.86  fof(f392,plain,(
% 3.68/0.86    k1_xboole_0 = sK2 | ~r1_tarski(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)),sK2) | ~spl4_3),
% 3.68/0.86    inference(forward_demodulation,[],[f391,f101])).
% 3.68/0.86  fof(f391,plain,(
% 3.68/0.86    sK2 = k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0) | ~r1_tarski(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)),sK2) | ~spl4_3),
% 3.68/0.86    inference(forward_demodulation,[],[f388,f225])).
% 3.68/0.86  fof(f388,plain,(
% 3.68/0.86    sK2 = k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)) | ~r1_tarski(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)),sK2)),
% 3.68/0.86    inference(resolution,[],[f113,f77])).
% 3.68/0.86  fof(f113,plain,(
% 3.68/0.86    r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))),
% 3.68/0.86    inference(forward_demodulation,[],[f112,f106])).
% 3.68/0.86  fof(f112,plain,(
% 3.68/0.86    r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))),
% 3.68/0.86    inference(forward_demodulation,[],[f109,f107])).
% 3.68/0.86  fof(f109,plain,(
% 3.68/0.86    r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))),
% 3.68/0.86    inference(resolution,[],[f78,f62])).
% 3.68/0.86  fof(f230,plain,(
% 3.68/0.86    spl4_3 | spl4_4),
% 3.68/0.86    inference(avatar_split_clause,[],[f221,f227,f223])).
% 3.68/0.86  fof(f221,plain,(
% 3.68/0.86    k2_struct_0(sK0) = k1_relat_1(sK2) | k1_xboole_0 = k2_struct_0(sK1)),
% 3.68/0.86    inference(forward_demodulation,[],[f220,f184])).
% 3.68/0.86  fof(f184,plain,(
% 3.68/0.86    k1_relat_1(sK2) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 3.68/0.86    inference(forward_demodulation,[],[f183,f136])).
% 3.68/0.86  fof(f136,plain,(
% 3.68/0.86    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 3.68/0.86    inference(forward_demodulation,[],[f135,f106])).
% 3.68/0.86  fof(f135,plain,(
% 3.68/0.86    k1_relat_1(sK2) = k1_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 3.68/0.86    inference(forward_demodulation,[],[f131,f107])).
% 3.68/0.86  fof(f131,plain,(
% 3.68/0.86    k1_relat_1(sK2) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 3.68/0.86    inference(resolution,[],[f84,f62])).
% 3.68/0.86  fof(f183,plain,(
% 3.68/0.86    k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 3.68/0.86    inference(forward_demodulation,[],[f182,f106])).
% 3.68/0.86  fof(f182,plain,(
% 3.68/0.86    k1_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 3.68/0.86    inference(forward_demodulation,[],[f178,f107])).
% 3.68/0.86  fof(f178,plain,(
% 3.68/0.86    k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK1))),
% 3.68/0.86    inference(resolution,[],[f89,f62])).
% 3.68/0.86  fof(f220,plain,(
% 3.68/0.86    k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | k1_xboole_0 = k2_struct_0(sK1)),
% 3.68/0.86    inference(forward_demodulation,[],[f219,f106])).
% 3.68/0.86  fof(f219,plain,(
% 3.68/0.86    u1_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | k1_xboole_0 = k2_struct_0(sK1)),
% 3.68/0.86    inference(forward_demodulation,[],[f218,f107])).
% 3.68/0.86  fof(f218,plain,(
% 3.68/0.86    k1_xboole_0 = k2_struct_0(sK1) | u1_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK1))),
% 3.68/0.86    inference(forward_demodulation,[],[f217,f107])).
% 3.68/0.86  fof(f217,plain,(
% 3.68/0.86    k1_xboole_0 = u1_struct_0(sK1) | u1_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK1))),
% 3.68/0.86    inference(subsumption_resolution,[],[f216,f60])).
% 3.68/0.86  fof(f216,plain,(
% 3.68/0.86    k1_xboole_0 = u1_struct_0(sK1) | u1_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 3.68/0.86    inference(subsumption_resolution,[],[f212,f61])).
% 3.68/0.86  fof(f212,plain,(
% 3.68/0.86    k1_xboole_0 = u1_struct_0(sK1) | u1_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK1)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 3.68/0.86    inference(resolution,[],[f97,f62])).
% 3.68/0.86  fof(f97,plain,(
% 3.68/0.86    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k8_relset_1(X0,X1,X2,X1) = X0 | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.68/0.86    inference(cnf_transformation,[],[f47])).
% 3.68/0.86  fof(f47,plain,(
% 3.68/0.86    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.68/0.86    inference(flattening,[],[f46])).
% 3.68/0.86  fof(f46,plain,(
% 3.68/0.86    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.68/0.86    inference(ennf_transformation,[],[f15])).
% 3.68/0.86  fof(f15,axiom,(
% 3.68/0.86    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 3.68/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).
% 3.68/0.86  % SZS output end Proof for theBenchmark
% 3.68/0.86  % (29214)------------------------------
% 3.68/0.86  % (29214)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.68/0.86  % (29214)Termination reason: Refutation
% 3.68/0.86  
% 3.68/0.86  % (29214)Memory used [KB]: 14456
% 3.68/0.86  % (29214)Time elapsed: 0.440 s
% 3.68/0.86  % (29214)------------------------------
% 3.68/0.86  % (29214)------------------------------
% 3.68/0.87  % (29203)Success in time 0.501 s
%------------------------------------------------------------------------------
