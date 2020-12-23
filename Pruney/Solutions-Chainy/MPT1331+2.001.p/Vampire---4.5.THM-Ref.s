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
% DateTime   : Thu Dec  3 13:13:59 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 231 expanded)
%              Number of leaves         :   20 (  91 expanded)
%              Depth                    :   13
%              Number of atoms          :  318 (1438 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f306,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f223,f268,f273,f297,f305])).

fof(f305,plain,(
    ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f304])).

fof(f304,plain,
    ( $false
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f303,f40])).

fof(f40,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ~ m1_subset_1(k9_relat_1(k3_funct_3(sK2),sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f35,f34,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
                & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ m1_subset_1(k9_relat_1(k3_funct_3(sK2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X3] :
        ( ~ m1_subset_1(k9_relat_1(k3_funct_3(sK2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
   => ( ~ m1_subset_1(k9_relat_1(k3_funct_3(sK2),sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( ( l1_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                   => m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                 => m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_2)).

fof(f303,plain,
    ( v2_struct_0(sK1)
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f302,f41])).

fof(f41,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f302,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_10 ),
    inference(resolution,[],[f278,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f278,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f277])).

fof(f277,plain,
    ( spl4_10
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f297,plain,
    ( spl4_10
    | spl4_2 ),
    inference(avatar_split_clause,[],[f296,f108,f277])).

fof(f108,plain,
    ( spl4_2
  <=> v1_partfun1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f296,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(k2_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f295,f42])).

fof(f42,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f295,plain,
    ( ~ v1_funct_1(sK2)
    | v1_partfun1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(k2_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f124,f74])).

fof(f74,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f68,f41])).

fof(f68,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ l1_struct_0(sK1) ),
    inference(superposition,[],[f43,f47])).

fof(f47,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f43,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f124,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | v1_partfun1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(k2_struct_0(sK1)) ),
    inference(resolution,[],[f72,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_partfun1(X2,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f66,f41])).

fof(f66,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ l1_struct_0(sK1) ),
    inference(superposition,[],[f44,f47])).

fof(f44,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f36])).

fof(f273,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f272])).

fof(f272,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f271,f83])).

fof(f83,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f60,f44])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f271,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_5 ),
    inference(subsumption_resolution,[],[f270,f42])).

fof(f270,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_5 ),
    inference(resolution,[],[f219,f51])).

fof(f51,plain,(
    ! [X0] :
      ( v1_relat_1(k3_funct_3(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k3_funct_3(X0))
        & v1_relat_1(k3_funct_3(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k3_funct_3(X0))
        & v1_relat_1(k3_funct_3(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k3_funct_3(X0))
        & v1_relat_1(k3_funct_3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_3)).

fof(f219,plain,
    ( ~ v1_relat_1(k3_funct_3(sK2))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl4_5
  <=> v1_relat_1(k3_funct_3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f268,plain,
    ( ~ spl4_2
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f267])).

fof(f267,plain,
    ( $false
    | ~ spl4_2
    | spl4_6 ),
    inference(subsumption_resolution,[],[f266,f85])).

fof(f85,plain,(
    v4_relat_1(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f61,f44])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f266,plain,
    ( ~ v4_relat_1(sK2,u1_struct_0(sK0))
    | ~ spl4_2
    | spl4_6 ),
    inference(subsumption_resolution,[],[f265,f109])).

fof(f109,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f108])).

fof(f265,plain,
    ( ~ v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ v4_relat_1(sK2,u1_struct_0(sK0))
    | spl4_6 ),
    inference(subsumption_resolution,[],[f264,f83])).

fof(f264,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ v4_relat_1(sK2,u1_struct_0(sK0))
    | spl4_6 ),
    inference(subsumption_resolution,[],[f261,f42])).

fof(f261,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ v4_relat_1(sK2,u1_struct_0(sK0))
    | spl4_6 ),
    inference(resolution,[],[f222,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k3_funct_3(X0)),k1_zfmisc_1(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_partfun1(X0,X1)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k3_funct_3(X0)),k1_zfmisc_1(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_partfun1(X0,X1)
      | ~ v4_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f50,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f50,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k3_funct_3(X0)),k1_zfmisc_1(k1_relat_1(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k3_funct_3(X0)),k1_zfmisc_1(k1_relat_1(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k3_funct_3(X0)),k1_zfmisc_1(k1_relat_1(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => r1_tarski(k2_relat_1(k3_funct_3(X0)),k1_zfmisc_1(k1_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_funct_3)).

fof(f222,plain,
    ( ~ r1_tarski(k2_relat_1(k3_funct_3(sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl4_6
  <=> r1_tarski(k2_relat_1(k3_funct_3(sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f223,plain,
    ( ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f214,f221,f218])).

fof(f214,plain,
    ( ~ r1_tarski(k2_relat_1(k3_funct_3(sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_relat_1(k3_funct_3(sK2)) ),
    inference(resolution,[],[f152,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

fof(f152,plain,(
    ! [X0] :
      ( ~ r1_tarski(k9_relat_1(k3_funct_3(sK2),sK3),X0)
      | ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f146,f39])).

fof(f39,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f146,plain,(
    ! [X0] :
      ( ~ r1_tarski(k9_relat_1(k3_funct_3(sK2),sK3),X0)
      | ~ l1_struct_0(sK0)
      | ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f96,f46])).

fof(f46,plain,(
    ~ m1_subset_1(k9_relat_1(k3_funct_3(sK2),sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f36])).

fof(f96,plain,(
    ! [X2,X3,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
      | ~ r1_tarski(X1,X2)
      | ~ l1_struct_0(X3)
      | ~ r1_tarski(X2,k1_zfmisc_1(u1_struct_0(X3))) ) ),
    inference(resolution,[],[f48,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r1_tarski(X2,X1)
      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              | ~ r1_tarski(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( r1_tarski(X2,X1)
             => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_tops_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : run_vampire %s %d
% 0.10/0.32  % Computer   : n017.cluster.edu
% 0.10/0.32  % Model      : x86_64 x86_64
% 0.10/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.32  % Memory     : 8042.1875MB
% 0.10/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.32  % CPULimit   : 60
% 0.10/0.32  % WCLimit    : 600
% 0.10/0.32  % DateTime   : Tue Dec  1 17:43:46 EST 2020
% 0.10/0.32  % CPUTime    : 
% 0.17/0.43  % (11983)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.17/0.43  % (11977)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.17/0.44  % (11969)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.17/0.44  % (11969)Refutation found. Thanks to Tanya!
% 0.17/0.44  % SZS status Theorem for theBenchmark
% 0.17/0.44  % SZS output start Proof for theBenchmark
% 0.17/0.45  fof(f306,plain,(
% 0.17/0.45    $false),
% 0.17/0.45    inference(avatar_sat_refutation,[],[f223,f268,f273,f297,f305])).
% 0.17/0.45  fof(f305,plain,(
% 0.17/0.45    ~spl4_10),
% 0.17/0.45    inference(avatar_contradiction_clause,[],[f304])).
% 0.17/0.45  fof(f304,plain,(
% 0.17/0.45    $false | ~spl4_10),
% 0.17/0.45    inference(subsumption_resolution,[],[f303,f40])).
% 0.17/0.45  fof(f40,plain,(
% 0.17/0.45    ~v2_struct_0(sK1)),
% 0.17/0.45    inference(cnf_transformation,[],[f36])).
% 0.17/0.45  fof(f36,plain,(
% 0.17/0.45    (((~m1_subset_1(k9_relat_1(k3_funct_3(sK2),sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.17/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f35,f34,f33,f32])).
% 0.17/0.45  fof(f32,plain,(
% 0.17/0.45    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 0.17/0.45    introduced(choice_axiom,[])).
% 0.17/0.45  fof(f33,plain,(
% 0.17/0.45    ? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))),
% 0.17/0.45    introduced(choice_axiom,[])).
% 0.17/0.45  fof(f34,plain,(
% 0.17/0.45    ? [X2] : (? [X3] : (~m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (? [X3] : (~m1_subset_1(k9_relat_1(k3_funct_3(sK2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.17/0.45    introduced(choice_axiom,[])).
% 0.17/0.45  fof(f35,plain,(
% 0.17/0.45    ? [X3] : (~m1_subset_1(k9_relat_1(k3_funct_3(sK2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) => (~m1_subset_1(k9_relat_1(k3_funct_3(sK2),sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))),
% 0.17/0.45    introduced(choice_axiom,[])).
% 0.17/0.45  fof(f16,plain,(
% 0.17/0.45    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.17/0.45    inference(flattening,[],[f15])).
% 0.17/0.45  fof(f15,plain,(
% 0.17/0.45    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.17/0.45    inference(ennf_transformation,[],[f13])).
% 0.17/0.45  fof(f13,negated_conjecture,(
% 0.17/0.45    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.17/0.45    inference(negated_conjecture,[],[f12])).
% 0.17/0.45  fof(f12,conjecture,(
% 0.17/0.45    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_2)).
% 0.17/0.45  fof(f303,plain,(
% 0.17/0.45    v2_struct_0(sK1) | ~spl4_10),
% 0.17/0.45    inference(subsumption_resolution,[],[f302,f41])).
% 0.17/0.45  fof(f41,plain,(
% 0.17/0.45    l1_struct_0(sK1)),
% 0.17/0.45    inference(cnf_transformation,[],[f36])).
% 0.17/0.45  fof(f302,plain,(
% 0.17/0.45    ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl4_10),
% 0.17/0.45    inference(resolution,[],[f278,f49])).
% 0.17/0.45  fof(f49,plain,(
% 0.17/0.45    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f20])).
% 0.17/0.45  fof(f20,plain,(
% 0.17/0.45    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.17/0.45    inference(flattening,[],[f19])).
% 0.17/0.45  fof(f19,plain,(
% 0.17/0.45    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.17/0.45    inference(ennf_transformation,[],[f8])).
% 0.17/0.45  fof(f8,axiom,(
% 0.17/0.45    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.17/0.45  fof(f278,plain,(
% 0.17/0.45    v1_xboole_0(k2_struct_0(sK1)) | ~spl4_10),
% 0.17/0.45    inference(avatar_component_clause,[],[f277])).
% 0.17/0.45  fof(f277,plain,(
% 0.17/0.45    spl4_10 <=> v1_xboole_0(k2_struct_0(sK1))),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.17/0.45  fof(f297,plain,(
% 0.17/0.45    spl4_10 | spl4_2),
% 0.17/0.45    inference(avatar_split_clause,[],[f296,f108,f277])).
% 0.17/0.45  fof(f108,plain,(
% 0.17/0.45    spl4_2 <=> v1_partfun1(sK2,u1_struct_0(sK0))),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.17/0.45  fof(f296,plain,(
% 0.17/0.45    v1_partfun1(sK2,u1_struct_0(sK0)) | v1_xboole_0(k2_struct_0(sK1))),
% 0.17/0.45    inference(subsumption_resolution,[],[f295,f42])).
% 0.17/0.45  fof(f42,plain,(
% 0.17/0.45    v1_funct_1(sK2)),
% 0.17/0.45    inference(cnf_transformation,[],[f36])).
% 0.17/0.45  fof(f295,plain,(
% 0.17/0.45    ~v1_funct_1(sK2) | v1_partfun1(sK2,u1_struct_0(sK0)) | v1_xboole_0(k2_struct_0(sK1))),
% 0.17/0.45    inference(subsumption_resolution,[],[f124,f74])).
% 0.17/0.45  fof(f74,plain,(
% 0.17/0.45    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))),
% 0.17/0.45    inference(subsumption_resolution,[],[f68,f41])).
% 0.17/0.45  fof(f68,plain,(
% 0.17/0.45    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | ~l1_struct_0(sK1)),
% 0.17/0.45    inference(superposition,[],[f43,f47])).
% 0.17/0.45  fof(f47,plain,(
% 0.17/0.45    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f17])).
% 0.17/0.45  fof(f17,plain,(
% 0.17/0.45    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.17/0.45    inference(ennf_transformation,[],[f7])).
% 0.17/0.45  fof(f7,axiom,(
% 0.17/0.45    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.17/0.45  fof(f43,plain,(
% 0.17/0.45    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.17/0.45    inference(cnf_transformation,[],[f36])).
% 0.17/0.45  fof(f124,plain,(
% 0.17/0.45    ~v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | v1_partfun1(sK2,u1_struct_0(sK0)) | v1_xboole_0(k2_struct_0(sK1))),
% 0.17/0.45    inference(resolution,[],[f72,f54])).
% 0.17/0.45  fof(f54,plain,(
% 0.17/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_partfun1(X2,X0) | v1_xboole_0(X1)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f26])).
% 0.17/0.45  fof(f26,plain,(
% 0.17/0.45    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.17/0.45    inference(flattening,[],[f25])).
% 0.17/0.45  fof(f25,plain,(
% 0.17/0.45    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.17/0.45    inference(ennf_transformation,[],[f5])).
% 0.17/0.45  fof(f5,axiom,(
% 0.17/0.45    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.17/0.45  fof(f72,plain,(
% 0.17/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))),
% 0.17/0.45    inference(subsumption_resolution,[],[f66,f41])).
% 0.17/0.45  fof(f66,plain,(
% 0.17/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | ~l1_struct_0(sK1)),
% 0.17/0.45    inference(superposition,[],[f44,f47])).
% 0.17/0.45  fof(f44,plain,(
% 0.17/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.17/0.45    inference(cnf_transformation,[],[f36])).
% 0.17/0.45  fof(f273,plain,(
% 0.17/0.45    spl4_5),
% 0.17/0.45    inference(avatar_contradiction_clause,[],[f272])).
% 0.17/0.45  fof(f272,plain,(
% 0.17/0.45    $false | spl4_5),
% 0.17/0.45    inference(subsumption_resolution,[],[f271,f83])).
% 0.17/0.45  fof(f83,plain,(
% 0.17/0.45    v1_relat_1(sK2)),
% 0.17/0.45    inference(resolution,[],[f60,f44])).
% 0.17/0.45  fof(f60,plain,(
% 0.17/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f30])).
% 0.17/0.45  fof(f30,plain,(
% 0.17/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.17/0.45    inference(ennf_transformation,[],[f3])).
% 0.17/0.45  fof(f3,axiom,(
% 0.17/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.17/0.45  fof(f271,plain,(
% 0.17/0.45    ~v1_relat_1(sK2) | spl4_5),
% 0.17/0.45    inference(subsumption_resolution,[],[f270,f42])).
% 0.17/0.45  fof(f270,plain,(
% 0.17/0.45    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_5),
% 0.17/0.45    inference(resolution,[],[f219,f51])).
% 0.17/0.45  fof(f51,plain,(
% 0.17/0.45    ( ! [X0] : (v1_relat_1(k3_funct_3(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f24])).
% 0.17/0.45  fof(f24,plain,(
% 0.17/0.45    ! [X0] : ((v1_funct_1(k3_funct_3(X0)) & v1_relat_1(k3_funct_3(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.17/0.45    inference(flattening,[],[f23])).
% 0.17/0.45  fof(f23,plain,(
% 0.17/0.45    ! [X0] : ((v1_funct_1(k3_funct_3(X0)) & v1_relat_1(k3_funct_3(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.17/0.45    inference(ennf_transformation,[],[f9])).
% 0.17/0.45  fof(f9,axiom,(
% 0.17/0.45    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k3_funct_3(X0)) & v1_relat_1(k3_funct_3(X0))))),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_3)).
% 0.17/0.45  fof(f219,plain,(
% 0.17/0.45    ~v1_relat_1(k3_funct_3(sK2)) | spl4_5),
% 0.17/0.45    inference(avatar_component_clause,[],[f218])).
% 0.17/0.45  fof(f218,plain,(
% 0.17/0.45    spl4_5 <=> v1_relat_1(k3_funct_3(sK2))),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.17/0.45  fof(f268,plain,(
% 0.17/0.45    ~spl4_2 | spl4_6),
% 0.17/0.45    inference(avatar_contradiction_clause,[],[f267])).
% 0.17/0.45  fof(f267,plain,(
% 0.17/0.45    $false | (~spl4_2 | spl4_6)),
% 0.17/0.45    inference(subsumption_resolution,[],[f266,f85])).
% 0.17/0.45  fof(f85,plain,(
% 0.17/0.45    v4_relat_1(sK2,u1_struct_0(sK0))),
% 0.17/0.45    inference(resolution,[],[f61,f44])).
% 0.17/0.45  fof(f61,plain,(
% 0.17/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f31])).
% 0.17/0.45  fof(f31,plain,(
% 0.17/0.45    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.17/0.45    inference(ennf_transformation,[],[f14])).
% 0.17/0.45  fof(f14,plain,(
% 0.17/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.17/0.45    inference(pure_predicate_removal,[],[f4])).
% 0.17/0.45  fof(f4,axiom,(
% 0.17/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.17/0.45  fof(f266,plain,(
% 0.17/0.45    ~v4_relat_1(sK2,u1_struct_0(sK0)) | (~spl4_2 | spl4_6)),
% 0.17/0.45    inference(subsumption_resolution,[],[f265,f109])).
% 0.17/0.45  fof(f109,plain,(
% 0.17/0.45    v1_partfun1(sK2,u1_struct_0(sK0)) | ~spl4_2),
% 0.17/0.45    inference(avatar_component_clause,[],[f108])).
% 0.17/0.45  fof(f265,plain,(
% 0.17/0.45    ~v1_partfun1(sK2,u1_struct_0(sK0)) | ~v4_relat_1(sK2,u1_struct_0(sK0)) | spl4_6),
% 0.17/0.45    inference(subsumption_resolution,[],[f264,f83])).
% 0.17/0.45  fof(f264,plain,(
% 0.17/0.45    ~v1_relat_1(sK2) | ~v1_partfun1(sK2,u1_struct_0(sK0)) | ~v4_relat_1(sK2,u1_struct_0(sK0)) | spl4_6),
% 0.17/0.45    inference(subsumption_resolution,[],[f261,f42])).
% 0.17/0.45  fof(f261,plain,(
% 0.17/0.45    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_partfun1(sK2,u1_struct_0(sK0)) | ~v4_relat_1(sK2,u1_struct_0(sK0)) | spl4_6),
% 0.17/0.45    inference(resolution,[],[f222,f93])).
% 0.17/0.45  fof(f93,plain,(
% 0.17/0.45    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k3_funct_3(X0)),k1_zfmisc_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_partfun1(X0,X1) | ~v4_relat_1(X0,X1)) )),
% 0.17/0.45    inference(duplicate_literal_removal,[],[f90])).
% 0.17/0.45  fof(f90,plain,(
% 0.17/0.45    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k3_funct_3(X0)),k1_zfmisc_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_partfun1(X0,X1) | ~v4_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.17/0.45    inference(superposition,[],[f50,f56])).
% 0.17/0.45  fof(f56,plain,(
% 0.17/0.45    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f37])).
% 0.17/0.45  fof(f37,plain,(
% 0.17/0.45    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.17/0.45    inference(nnf_transformation,[],[f29])).
% 0.17/0.45  fof(f29,plain,(
% 0.17/0.45    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.17/0.45    inference(flattening,[],[f28])).
% 0.17/0.45  fof(f28,plain,(
% 0.17/0.45    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.17/0.45    inference(ennf_transformation,[],[f6])).
% 0.17/0.45  fof(f6,axiom,(
% 0.17/0.45    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 0.17/0.45  fof(f50,plain,(
% 0.17/0.45    ( ! [X0] : (r1_tarski(k2_relat_1(k3_funct_3(X0)),k1_zfmisc_1(k1_relat_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f22])).
% 0.17/0.45  fof(f22,plain,(
% 0.17/0.45    ! [X0] : (r1_tarski(k2_relat_1(k3_funct_3(X0)),k1_zfmisc_1(k1_relat_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.17/0.45    inference(flattening,[],[f21])).
% 0.17/0.45  fof(f21,plain,(
% 0.17/0.45    ! [X0] : (r1_tarski(k2_relat_1(k3_funct_3(X0)),k1_zfmisc_1(k1_relat_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.17/0.45    inference(ennf_transformation,[],[f10])).
% 0.17/0.45  fof(f10,axiom,(
% 0.17/0.45    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => r1_tarski(k2_relat_1(k3_funct_3(X0)),k1_zfmisc_1(k1_relat_1(X0))))),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_funct_3)).
% 0.17/0.45  fof(f222,plain,(
% 0.17/0.45    ~r1_tarski(k2_relat_1(k3_funct_3(sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_6),
% 0.17/0.45    inference(avatar_component_clause,[],[f221])).
% 0.17/0.45  fof(f221,plain,(
% 0.17/0.45    spl4_6 <=> r1_tarski(k2_relat_1(k3_funct_3(sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.17/0.45  fof(f223,plain,(
% 0.17/0.45    ~spl4_5 | ~spl4_6),
% 0.17/0.45    inference(avatar_split_clause,[],[f214,f221,f218])).
% 0.17/0.45  fof(f214,plain,(
% 0.17/0.45    ~r1_tarski(k2_relat_1(k3_funct_3(sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_relat_1(k3_funct_3(sK2))),
% 0.17/0.45    inference(resolution,[],[f152,f55])).
% 0.17/0.45  fof(f55,plain,(
% 0.17/0.45    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f27])).
% 0.17/0.45  fof(f27,plain,(
% 0.17/0.45    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.17/0.45    inference(ennf_transformation,[],[f2])).
% 0.17/0.45  fof(f2,axiom,(
% 0.17/0.45    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).
% 0.17/0.45  fof(f152,plain,(
% 0.17/0.45    ( ! [X0] : (~r1_tarski(k9_relat_1(k3_funct_3(sK2),sK3),X0) | ~r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.17/0.45    inference(subsumption_resolution,[],[f146,f39])).
% 0.17/0.45  fof(f39,plain,(
% 0.17/0.45    l1_struct_0(sK0)),
% 0.17/0.45    inference(cnf_transformation,[],[f36])).
% 0.17/0.45  fof(f146,plain,(
% 0.17/0.45    ( ! [X0] : (~r1_tarski(k9_relat_1(k3_funct_3(sK2),sK3),X0) | ~l1_struct_0(sK0) | ~r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.17/0.45    inference(resolution,[],[f96,f46])).
% 0.17/0.45  fof(f46,plain,(
% 0.17/0.45    ~m1_subset_1(k9_relat_1(k3_funct_3(sK2),sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.17/0.45    inference(cnf_transformation,[],[f36])).
% 0.17/0.45  fof(f96,plain,(
% 0.17/0.45    ( ! [X2,X3,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3)))) | ~r1_tarski(X1,X2) | ~l1_struct_0(X3) | ~r1_tarski(X2,k1_zfmisc_1(u1_struct_0(X3)))) )),
% 0.17/0.45    inference(resolution,[],[f48,f59])).
% 0.17/0.45  fof(f59,plain,(
% 0.17/0.45    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f38])).
% 0.17/0.45  fof(f38,plain,(
% 0.17/0.45    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.17/0.45    inference(nnf_transformation,[],[f1])).
% 0.17/0.45  fof(f1,axiom,(
% 0.17/0.45    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.17/0.45  fof(f48,plain,(
% 0.17/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f18])).
% 0.17/0.45  fof(f18,plain,(
% 0.17/0.45    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_struct_0(X0))),
% 0.17/0.45    inference(ennf_transformation,[],[f11])).
% 0.17/0.45  fof(f11,axiom,(
% 0.17/0.45    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (r1_tarski(X2,X1) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_tops_2)).
% 0.17/0.45  % SZS output end Proof for theBenchmark
% 0.17/0.45  % (11969)------------------------------
% 0.17/0.45  % (11969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.45  % (11969)Termination reason: Refutation
% 0.17/0.45  
% 0.17/0.45  % (11969)Memory used [KB]: 10746
% 0.17/0.45  % (11969)Time elapsed: 0.067 s
% 0.17/0.45  % (11969)------------------------------
% 0.17/0.45  % (11969)------------------------------
% 0.17/0.45  % (11966)Success in time 0.116 s
%------------------------------------------------------------------------------
