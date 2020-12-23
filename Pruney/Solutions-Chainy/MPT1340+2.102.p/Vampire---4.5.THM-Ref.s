%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 801 expanded)
%              Number of leaves         :   23 ( 294 expanded)
%              Depth                    :   22
%              Number of atoms          :  692 (6254 expanded)
%              Number of equality atoms :   94 ( 827 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f741,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f163,f294,f360,f409,f462,f466,f512,f582,f740])).

fof(f740,plain,
    ( ~ spl5_2
    | spl5_31 ),
    inference(avatar_contradiction_clause,[],[f739])).

fof(f739,plain,
    ( $false
    | ~ spl5_2
    | spl5_31 ),
    inference(subsumption_resolution,[],[f738,f39])).

fof(f39,plain,(
    l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK4)
    & v2_funct_1(sK4)
    & k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK4)
    & l1_struct_0(sK3)
    & ~ v2_struct_0(sK3)
    & l1_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f13,f34,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
                & v2_funct_1(X2)
                & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X2)),X2)
            & v2_funct_1(X2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2)),X2)
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X2) = k2_struct_0(sK3)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
          & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
          & v1_funct_1(X2) )
      & l1_struct_0(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X2] :
        ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2)),X2)
        & v2_funct_1(X2)
        & k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X2) = k2_struct_0(sK3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
        & v1_funct_1(X2) )
   => ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK4)
      & v2_funct_1(sK4)
      & k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f738,plain,
    ( ~ l1_struct_0(sK2)
    | ~ spl5_2
    | spl5_31 ),
    inference(trivial_inequality_removal,[],[f737])).

fof(f737,plain,
    ( k2_struct_0(sK2) != k2_struct_0(sK2)
    | ~ l1_struct_0(sK2)
    | ~ spl5_2
    | spl5_31 ),
    inference(superposition,[],[f734,f48])).

fof(f48,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f734,plain,
    ( u1_struct_0(sK2) != k2_struct_0(sK2)
    | ~ spl5_2
    | spl5_31 ),
    inference(subsumption_resolution,[],[f733,f39])).

fof(f733,plain,
    ( u1_struct_0(sK2) != k2_struct_0(sK2)
    | ~ l1_struct_0(sK2)
    | ~ spl5_2
    | spl5_31 ),
    inference(subsumption_resolution,[],[f732,f42])).

fof(f42,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f732,plain,
    ( u1_struct_0(sK2) != k2_struct_0(sK2)
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK2)
    | ~ spl5_2
    | spl5_31 ),
    inference(subsumption_resolution,[],[f731,f82])).

fof(f82,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f74,f41])).

fof(f41,plain,(
    l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f74,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))
    | ~ l1_struct_0(sK3) ),
    inference(superposition,[],[f43,f48])).

fof(f43,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f35])).

fof(f731,plain,
    ( u1_struct_0(sK2) != k2_struct_0(sK2)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK2)
    | ~ spl5_2
    | spl5_31 ),
    inference(subsumption_resolution,[],[f730,f81])).

fof(f81,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3)))) ),
    inference(subsumption_resolution,[],[f73,f41])).

fof(f73,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3))))
    | ~ l1_struct_0(sK3) ),
    inference(superposition,[],[f44,f48])).

fof(f44,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f730,plain,
    ( u1_struct_0(sK2) != k2_struct_0(sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK2)
    | ~ spl5_2
    | spl5_31 ),
    inference(subsumption_resolution,[],[f729,f80])).

fof(f80,plain,(
    k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4) ),
    inference(subsumption_resolution,[],[f72,f41])).

fof(f72,plain,
    ( k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ l1_struct_0(sK3) ),
    inference(superposition,[],[f45,f48])).

fof(f45,plain,(
    k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f729,plain,
    ( u1_struct_0(sK2) != k2_struct_0(sK2)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK2)
    | ~ spl5_2
    | spl5_31 ),
    inference(subsumption_resolution,[],[f725,f46])).

fof(f46,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f725,plain,
    ( u1_struct_0(sK2) != k2_struct_0(sK2)
    | ~ v2_funct_1(sK4)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK2)
    | ~ spl5_2
    | spl5_31 ),
    inference(superposition,[],[f453,f699])).

fof(f699,plain,
    ( ! [X4,X3] :
        ( k2_struct_0(X3) = k2_relset_1(k2_struct_0(sK3),u1_struct_0(X3),k2_funct_1(X4))
        | ~ v2_funct_1(X4)
        | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(X3),k2_struct_0(sK3),X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK3))))
        | ~ v1_funct_2(X4,u1_struct_0(X3),k2_struct_0(sK3))
        | ~ v1_funct_1(X4)
        | ~ l1_struct_0(X3) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f698,f40])).

fof(f40,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f698,plain,
    ( ! [X4,X3] :
        ( k2_struct_0(X3) = k2_relset_1(k2_struct_0(sK3),u1_struct_0(X3),k2_funct_1(X4))
        | ~ v2_funct_1(X4)
        | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(X3),k2_struct_0(sK3),X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK3))))
        | ~ v1_funct_2(X4,u1_struct_0(X3),k2_struct_0(sK3))
        | ~ v1_funct_1(X4)
        | v2_struct_0(sK3)
        | ~ l1_struct_0(X3) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f691,f41])).

fof(f691,plain,
    ( ! [X4,X3] :
        ( k2_struct_0(X3) = k2_relset_1(k2_struct_0(sK3),u1_struct_0(X3),k2_funct_1(X4))
        | ~ v2_funct_1(X4)
        | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(X3),k2_struct_0(sK3),X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK3))))
        | ~ v1_funct_2(X4,u1_struct_0(X3),k2_struct_0(sK3))
        | ~ v1_funct_1(X4)
        | ~ l1_struct_0(sK3)
        | v2_struct_0(sK3)
        | ~ l1_struct_0(X3) )
    | ~ spl5_2 ),
    inference(superposition,[],[f438,f146])).

fof(f146,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl5_2
  <=> u1_struct_0(sK3) = k2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f438,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_funct_1(X2))
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f437,f48])).

fof(f437,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_funct_1(X2))
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | u1_struct_0(X1) != k2_struct_0(X1) ) ),
    inference(inner_rewriting,[],[f431])).

fof(f431,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_funct_1(X2))
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | u1_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) ),
    inference(duplicate_literal_removal,[],[f430])).

fof(f430,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_funct_1(X2))
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | ~ v2_funct_1(X2)
      | u1_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2) ) ),
    inference(superposition,[],[f50,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
               => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                  & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

fof(f453,plain,
    ( u1_struct_0(sK2) != k2_relset_1(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4))
    | spl5_31 ),
    inference(avatar_component_clause,[],[f451])).

fof(f451,plain,
    ( spl5_31
  <=> u1_struct_0(sK2) = k2_relset_1(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f582,plain,(
    spl5_33 ),
    inference(avatar_contradiction_clause,[],[f581])).

fof(f581,plain,
    ( $false
    | spl5_33 ),
    inference(subsumption_resolution,[],[f580,f95])).

fof(f95,plain,(
    v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f91,f57])).

fof(f57,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f91,plain,
    ( v1_relat_1(sK4)
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) ),
    inference(resolution,[],[f51,f44])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f580,plain,
    ( ~ v1_relat_1(sK4)
    | spl5_33 ),
    inference(subsumption_resolution,[],[f579,f42])).

fof(f579,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | spl5_33 ),
    inference(subsumption_resolution,[],[f578,f46])).

fof(f578,plain,
    ( ~ v2_funct_1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | spl5_33 ),
    inference(subsumption_resolution,[],[f576,f125])).

fof(f125,plain,(
    r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4,sK4) ),
    inference(subsumption_resolution,[],[f124,f42])).

fof(f124,plain,
    ( r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4,sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f117,f82])).

fof(f117,plain,
    ( r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4,sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f66,f81])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f65])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f576,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4,sK4)
    | ~ v2_funct_1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | spl5_33 ),
    inference(superposition,[],[f461,f56])).

fof(f56,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(f461,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_funct_1(k2_funct_1(sK4)),sK4)
    | spl5_33 ),
    inference(avatar_component_clause,[],[f459])).

fof(f459,plain,
    ( spl5_33
  <=> r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_funct_1(k2_funct_1(sK4)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f512,plain,(
    spl5_32 ),
    inference(avatar_contradiction_clause,[],[f511])).

fof(f511,plain,
    ( $false
    | spl5_32 ),
    inference(subsumption_resolution,[],[f510,f95])).

fof(f510,plain,
    ( ~ v1_relat_1(sK4)
    | spl5_32 ),
    inference(subsumption_resolution,[],[f509,f42])).

fof(f509,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | spl5_32 ),
    inference(subsumption_resolution,[],[f508,f46])).

fof(f508,plain,
    ( ~ v2_funct_1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | spl5_32 ),
    inference(resolution,[],[f507,f55])).

fof(f55,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f19,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ sP0(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f19,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f507,plain,
    ( ~ sP0(sK4)
    | spl5_32 ),
    inference(resolution,[],[f457,f54])).

fof(f54,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f457,plain,
    ( ~ v2_funct_1(k2_funct_1(sK4))
    | spl5_32 ),
    inference(avatar_component_clause,[],[f455])).

fof(f455,plain,
    ( spl5_32
  <=> v2_funct_1(k2_funct_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f466,plain,
    ( ~ spl5_1
    | spl5_30 ),
    inference(avatar_contradiction_clause,[],[f465])).

fof(f465,plain,
    ( $false
    | ~ spl5_1
    | spl5_30 ),
    inference(subsumption_resolution,[],[f463,f143])).

fof(f143,plain,
    ( sP1(u1_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl5_1
  <=> sP1(u1_struct_0(sK2),k2_struct_0(sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f463,plain,
    ( ~ sP1(u1_struct_0(sK2),k2_struct_0(sK3),sK4)
    | spl5_30 ),
    inference(resolution,[],[f449,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | ~ sP1(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f449,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK2))))
    | spl5_30 ),
    inference(avatar_component_clause,[],[f447])).

fof(f447,plain,
    ( spl5_30
  <=> m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f462,plain,
    ( ~ spl5_30
    | ~ spl5_31
    | ~ spl5_32
    | ~ spl5_33
    | ~ spl5_1
    | spl5_4
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f445,f244,f199,f141,f459,f455,f451,f447])).

fof(f199,plain,
    ( spl5_4
  <=> r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f244,plain,
    ( spl5_13
  <=> v1_funct_2(k2_tops_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4),k2_struct_0(sK3),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f445,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_funct_1(k2_funct_1(sK4)),sK4)
    | ~ v2_funct_1(k2_funct_1(sK4))
    | u1_struct_0(sK2) != k2_relset_1(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4))
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK2))))
    | ~ spl5_1
    | spl5_4
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f444,f176])).

fof(f176,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ spl5_1 ),
    inference(resolution,[],[f143,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | v1_funct_1(k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f444,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_funct_1(k2_funct_1(sK4)),sK4)
    | ~ v2_funct_1(k2_funct_1(sK4))
    | u1_struct_0(sK2) != k2_relset_1(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4))
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | spl5_4
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f441,f421])).

fof(f421,plain,
    ( v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),u1_struct_0(sK2))
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f420,f42])).

fof(f420,plain,
    ( v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_1(sK4)
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f419,f82])).

fof(f419,plain,
    ( v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f418,f81])).

fof(f418,plain,
    ( v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f417,f80])).

fof(f417,plain,
    ( v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),u1_struct_0(sK2))
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f415,f46])).

fof(f415,plain,
    ( v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),u1_struct_0(sK2))
    | ~ v2_funct_1(sK4)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ spl5_13 ),
    inference(superposition,[],[f245,f62])).

fof(f245,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4),k2_struct_0(sK3),u1_struct_0(sK2))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f244])).

fof(f441,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_funct_1(k2_funct_1(sK4)),sK4)
    | ~ v2_funct_1(k2_funct_1(sK4))
    | u1_struct_0(sK2) != k2_relset_1(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4))
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | spl5_4 ),
    inference(superposition,[],[f201,f62])).

fof(f201,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f199])).

fof(f409,plain,
    ( ~ spl5_1
    | spl5_13 ),
    inference(avatar_contradiction_clause,[],[f408])).

fof(f408,plain,
    ( $false
    | ~ spl5_1
    | spl5_13 ),
    inference(subsumption_resolution,[],[f406,f143])).

fof(f406,plain,
    ( ~ sP1(u1_struct_0(sK2),k2_struct_0(sK3),sK4)
    | spl5_13 ),
    inference(resolution,[],[f403,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f403,plain,
    ( ~ v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),u1_struct_0(sK2))
    | spl5_13 ),
    inference(subsumption_resolution,[],[f402,f42])).

fof(f402,plain,
    ( ~ v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_1(sK4)
    | spl5_13 ),
    inference(subsumption_resolution,[],[f401,f82])).

fof(f401,plain,
    ( ~ v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | spl5_13 ),
    inference(subsumption_resolution,[],[f400,f81])).

fof(f400,plain,
    ( ~ v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | spl5_13 ),
    inference(subsumption_resolution,[],[f399,f80])).

fof(f399,plain,
    ( ~ v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),u1_struct_0(sK2))
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | spl5_13 ),
    inference(subsumption_resolution,[],[f397,f46])).

fof(f397,plain,
    ( ~ v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),u1_struct_0(sK2))
    | ~ v2_funct_1(sK4)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | spl5_13 ),
    inference(superposition,[],[f246,f62])).

fof(f246,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4),k2_struct_0(sK3),u1_struct_0(sK2))
    | spl5_13 ),
    inference(avatar_component_clause,[],[f244])).

fof(f360,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f359])).

fof(f359,plain,
    ( $false
    | spl5_2 ),
    inference(subsumption_resolution,[],[f358,f41])).

fof(f358,plain,
    ( ~ l1_struct_0(sK3)
    | spl5_2 ),
    inference(trivial_inequality_removal,[],[f357])).

fof(f357,plain,
    ( k2_struct_0(sK3) != k2_struct_0(sK3)
    | ~ l1_struct_0(sK3)
    | spl5_2 ),
    inference(superposition,[],[f147,f48])).

fof(f147,plain,
    ( u1_struct_0(sK3) != k2_struct_0(sK3)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f145])).

fof(f294,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f293,f199])).

fof(f293,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4) ),
    inference(subsumption_resolution,[],[f292,f42])).

fof(f292,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f291,f82])).

fof(f291,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f290,f81])).

fof(f290,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f289,f80])).

fof(f289,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f189,f46])).

fof(f189,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4)
    | ~ v2_funct_1(sK4)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(superposition,[],[f79,f62])).

fof(f79,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4)),sK4) ),
    inference(subsumption_resolution,[],[f71,f41])).

fof(f71,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4)),sK4)
    | ~ l1_struct_0(sK3) ),
    inference(superposition,[],[f47,f48])).

fof(f47,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f163,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f162,f141])).

fof(f162,plain,(
    sP1(u1_struct_0(sK2),k2_struct_0(sK3),sK4) ),
    inference(subsumption_resolution,[],[f161,f42])).

fof(f161,plain,
    ( sP1(u1_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f160,f82])).

fof(f160,plain,
    ( sP1(u1_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f159,f46])).

fof(f159,plain,
    ( ~ v2_funct_1(sK4)
    | sP1(u1_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f132,f80])).

fof(f132,plain,
    ( k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ v2_funct_1(sK4)
    | sP1(u1_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f61,f81])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | sP1(X0,X1,X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f23,f30])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

% (4852)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:13:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.45  % (4849)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.46  % (4849)Refutation not found, incomplete strategy% (4849)------------------------------
% 0.22/0.46  % (4849)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (4849)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.46  
% 0.22/0.46  % (4849)Memory used [KB]: 6396
% 0.22/0.46  % (4849)Time elapsed: 0.010 s
% 0.22/0.46  % (4849)------------------------------
% 0.22/0.46  % (4849)------------------------------
% 0.22/0.48  % (4840)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.49  % (4844)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.50  % (4840)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f741,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f163,f294,f360,f409,f462,f466,f512,f582,f740])).
% 0.22/0.50  fof(f740,plain,(
% 0.22/0.50    ~spl5_2 | spl5_31),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f739])).
% 0.22/0.50  fof(f739,plain,(
% 0.22/0.50    $false | (~spl5_2 | spl5_31)),
% 0.22/0.50    inference(subsumption_resolution,[],[f738,f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    l1_struct_0(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK4) & v2_funct_1(sK4) & k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & l1_struct_0(sK3) & ~v2_struct_0(sK3)) & l1_struct_0(sK2)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f13,f34,f33,f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK2))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X2) = k2_struct_0(sK3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X2)) & l1_struct_0(sK3) & ~v2_struct_0(sK3))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ? [X2] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X2) = k2_struct_0(sK3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK4) & v2_funct_1(sK4) & k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,negated_conjecture,(
% 0.22/0.50    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.22/0.50    inference(negated_conjecture,[],[f10])).
% 0.22/0.50  fof(f10,conjecture,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).
% 0.22/0.50  fof(f738,plain,(
% 0.22/0.50    ~l1_struct_0(sK2) | (~spl5_2 | spl5_31)),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f737])).
% 0.22/0.50  fof(f737,plain,(
% 0.22/0.50    k2_struct_0(sK2) != k2_struct_0(sK2) | ~l1_struct_0(sK2) | (~spl5_2 | spl5_31)),
% 0.22/0.50    inference(superposition,[],[f734,f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.50  fof(f734,plain,(
% 0.22/0.50    u1_struct_0(sK2) != k2_struct_0(sK2) | (~spl5_2 | spl5_31)),
% 0.22/0.50    inference(subsumption_resolution,[],[f733,f39])).
% 0.22/0.50  fof(f733,plain,(
% 0.22/0.50    u1_struct_0(sK2) != k2_struct_0(sK2) | ~l1_struct_0(sK2) | (~spl5_2 | spl5_31)),
% 0.22/0.50    inference(subsumption_resolution,[],[f732,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    v1_funct_1(sK4)),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f732,plain,(
% 0.22/0.50    u1_struct_0(sK2) != k2_struct_0(sK2) | ~v1_funct_1(sK4) | ~l1_struct_0(sK2) | (~spl5_2 | spl5_31)),
% 0.22/0.50    inference(subsumption_resolution,[],[f731,f82])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))),
% 0.22/0.50    inference(subsumption_resolution,[],[f74,f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    l1_struct_0(sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) | ~l1_struct_0(sK3)),
% 0.22/0.50    inference(superposition,[],[f43,f48])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f731,plain,(
% 0.22/0.50    u1_struct_0(sK2) != k2_struct_0(sK2) | ~v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK2) | (~spl5_2 | spl5_31)),
% 0.22/0.50    inference(subsumption_resolution,[],[f730,f81])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3))))),
% 0.22/0.50    inference(subsumption_resolution,[],[f73,f41])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3)))) | ~l1_struct_0(sK3)),
% 0.22/0.50    inference(superposition,[],[f44,f48])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f730,plain,(
% 0.22/0.50    u1_struct_0(sK2) != k2_struct_0(sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK2) | (~spl5_2 | spl5_31)),
% 0.22/0.50    inference(subsumption_resolution,[],[f729,f80])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f72,f41])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4) | ~l1_struct_0(sK3)),
% 0.22/0.50    inference(superposition,[],[f45,f48])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f729,plain,(
% 0.22/0.50    u1_struct_0(sK2) != k2_struct_0(sK2) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK2) | (~spl5_2 | spl5_31)),
% 0.22/0.50    inference(subsumption_resolution,[],[f725,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    v2_funct_1(sK4)),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f725,plain,(
% 0.22/0.50    u1_struct_0(sK2) != k2_struct_0(sK2) | ~v2_funct_1(sK4) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK2) | (~spl5_2 | spl5_31)),
% 0.22/0.50    inference(superposition,[],[f453,f699])).
% 0.22/0.50  fof(f699,plain,(
% 0.22/0.50    ( ! [X4,X3] : (k2_struct_0(X3) = k2_relset_1(k2_struct_0(sK3),u1_struct_0(X3),k2_funct_1(X4)) | ~v2_funct_1(X4) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(X3),k2_struct_0(sK3),X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK3)))) | ~v1_funct_2(X4,u1_struct_0(X3),k2_struct_0(sK3)) | ~v1_funct_1(X4) | ~l1_struct_0(X3)) ) | ~spl5_2),
% 0.22/0.50    inference(subsumption_resolution,[],[f698,f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ~v2_struct_0(sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f698,plain,(
% 0.22/0.50    ( ! [X4,X3] : (k2_struct_0(X3) = k2_relset_1(k2_struct_0(sK3),u1_struct_0(X3),k2_funct_1(X4)) | ~v2_funct_1(X4) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(X3),k2_struct_0(sK3),X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK3)))) | ~v1_funct_2(X4,u1_struct_0(X3),k2_struct_0(sK3)) | ~v1_funct_1(X4) | v2_struct_0(sK3) | ~l1_struct_0(X3)) ) | ~spl5_2),
% 0.22/0.50    inference(subsumption_resolution,[],[f691,f41])).
% 0.22/0.50  fof(f691,plain,(
% 0.22/0.50    ( ! [X4,X3] : (k2_struct_0(X3) = k2_relset_1(k2_struct_0(sK3),u1_struct_0(X3),k2_funct_1(X4)) | ~v2_funct_1(X4) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(X3),k2_struct_0(sK3),X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK3)))) | ~v1_funct_2(X4,u1_struct_0(X3),k2_struct_0(sK3)) | ~v1_funct_1(X4) | ~l1_struct_0(sK3) | v2_struct_0(sK3) | ~l1_struct_0(X3)) ) | ~spl5_2),
% 0.22/0.50    inference(superposition,[],[f438,f146])).
% 0.22/0.50  fof(f146,plain,(
% 0.22/0.50    u1_struct_0(sK3) = k2_struct_0(sK3) | ~spl5_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f145])).
% 0.22/0.50  fof(f145,plain,(
% 0.22/0.50    spl5_2 <=> u1_struct_0(sK3) = k2_struct_0(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.50  fof(f438,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_funct_1(X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f437,f48])).
% 0.22/0.50  fof(f437,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_funct_1(X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | u1_struct_0(X1) != k2_struct_0(X1)) )),
% 0.22/0.50    inference(inner_rewriting,[],[f431])).
% 0.22/0.50  fof(f431,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_funct_1(X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | u1_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f430])).
% 0.22/0.50  fof(f430,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_funct_1(X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | ~v2_funct_1(X2) | u1_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) )),
% 0.22/0.50    inference(superposition,[],[f50,f62])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.50    inference(flattening,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_struct_0(X1) | v2_struct_0(X1))) | ~l1_struct_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).
% 0.22/0.50  fof(f453,plain,(
% 0.22/0.50    u1_struct_0(sK2) != k2_relset_1(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)) | spl5_31),
% 0.22/0.50    inference(avatar_component_clause,[],[f451])).
% 0.22/0.50  fof(f451,plain,(
% 0.22/0.50    spl5_31 <=> u1_struct_0(sK2) = k2_relset_1(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 0.22/0.50  fof(f582,plain,(
% 0.22/0.50    spl5_33),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f581])).
% 0.22/0.50  fof(f581,plain,(
% 0.22/0.50    $false | spl5_33),
% 0.22/0.50    inference(subsumption_resolution,[],[f580,f95])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    v1_relat_1(sK4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f91,f57])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    v1_relat_1(sK4) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))),
% 0.22/0.50    inference(resolution,[],[f51,f44])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.50  fof(f580,plain,(
% 0.22/0.50    ~v1_relat_1(sK4) | spl5_33),
% 0.22/0.50    inference(subsumption_resolution,[],[f579,f42])).
% 0.22/0.50  fof(f579,plain,(
% 0.22/0.50    ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | spl5_33),
% 0.22/0.50    inference(subsumption_resolution,[],[f578,f46])).
% 0.22/0.50  fof(f578,plain,(
% 0.22/0.50    ~v2_funct_1(sK4) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | spl5_33),
% 0.22/0.50    inference(subsumption_resolution,[],[f576,f125])).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4,sK4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f124,f42])).
% 0.22/0.50  fof(f124,plain,(
% 0.22/0.50    r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4,sK4) | ~v1_funct_1(sK4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f117,f82])).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4,sK4) | ~v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 0.22/0.50    inference(resolution,[],[f66,f81])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X3,X3) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f65])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.22/0.50    inference(equality_resolution,[],[f64])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.50    inference(nnf_transformation,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.50    inference(flattening,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 0.22/0.50  fof(f576,plain,(
% 0.22/0.50    ~r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4,sK4) | ~v2_funct_1(sK4) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | spl5_33),
% 0.22/0.50    inference(superposition,[],[f461,f56])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 0.22/0.50  fof(f461,plain,(
% 0.22/0.50    ~r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_funct_1(k2_funct_1(sK4)),sK4) | spl5_33),
% 0.22/0.50    inference(avatar_component_clause,[],[f459])).
% 0.22/0.50  fof(f459,plain,(
% 0.22/0.50    spl5_33 <=> r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_funct_1(k2_funct_1(sK4)),sK4)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 0.22/0.50  fof(f512,plain,(
% 0.22/0.50    spl5_32),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f511])).
% 0.22/0.50  fof(f511,plain,(
% 0.22/0.50    $false | spl5_32),
% 0.22/0.50    inference(subsumption_resolution,[],[f510,f95])).
% 0.22/0.50  fof(f510,plain,(
% 0.22/0.50    ~v1_relat_1(sK4) | spl5_32),
% 0.22/0.50    inference(subsumption_resolution,[],[f509,f42])).
% 0.22/0.50  fof(f509,plain,(
% 0.22/0.50    ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | spl5_32),
% 0.22/0.50    inference(subsumption_resolution,[],[f508,f46])).
% 0.22/0.50  fof(f508,plain,(
% 0.22/0.50    ~v2_funct_1(sK4) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | spl5_32),
% 0.22/0.50    inference(resolution,[],[f507,f55])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ( ! [X0] : (sP0(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0] : (sP0(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(definition_folding,[],[f19,f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~sP0(X0))),
% 0.22/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).
% 0.22/0.50  fof(f507,plain,(
% 0.22/0.50    ~sP0(sK4) | spl5_32),
% 0.22/0.50    inference(resolution,[],[f457,f54])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~sP0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~sP0(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f28])).
% 0.22/0.50  fof(f457,plain,(
% 0.22/0.50    ~v2_funct_1(k2_funct_1(sK4)) | spl5_32),
% 0.22/0.50    inference(avatar_component_clause,[],[f455])).
% 0.22/0.50  fof(f455,plain,(
% 0.22/0.50    spl5_32 <=> v2_funct_1(k2_funct_1(sK4))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 0.22/0.50  fof(f466,plain,(
% 0.22/0.50    ~spl5_1 | spl5_30),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f465])).
% 0.22/0.50  fof(f465,plain,(
% 0.22/0.50    $false | (~spl5_1 | spl5_30)),
% 0.22/0.50    inference(subsumption_resolution,[],[f463,f143])).
% 0.22/0.50  fof(f143,plain,(
% 0.22/0.50    sP1(u1_struct_0(sK2),k2_struct_0(sK3),sK4) | ~spl5_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f141])).
% 0.22/0.50  fof(f141,plain,(
% 0.22/0.50    spl5_1 <=> sP1(u1_struct_0(sK2),k2_struct_0(sK3),sK4)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.50  fof(f463,plain,(
% 0.22/0.50    ~sP1(u1_struct_0(sK2),k2_struct_0(sK3),sK4) | spl5_30),
% 0.22/0.50    inference(resolution,[],[f449,f60])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~sP1(X0,X1,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | ~sP1(X0,X1,X2))),
% 0.22/0.50    inference(nnf_transformation,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | ~sP1(X0,X1,X2))),
% 0.22/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.50  fof(f449,plain,(
% 0.22/0.50    ~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK2)))) | spl5_30),
% 0.22/0.50    inference(avatar_component_clause,[],[f447])).
% 0.22/0.50  fof(f447,plain,(
% 0.22/0.50    spl5_30 <=> m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK2))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.22/0.50  fof(f462,plain,(
% 0.22/0.50    ~spl5_30 | ~spl5_31 | ~spl5_32 | ~spl5_33 | ~spl5_1 | spl5_4 | ~spl5_13),
% 0.22/0.50    inference(avatar_split_clause,[],[f445,f244,f199,f141,f459,f455,f451,f447])).
% 0.22/0.50  fof(f199,plain,(
% 0.22/0.50    spl5_4 <=> r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.50  fof(f244,plain,(
% 0.22/0.50    spl5_13 <=> v1_funct_2(k2_tops_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4),k2_struct_0(sK3),u1_struct_0(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.22/0.50  fof(f445,plain,(
% 0.22/0.50    ~r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_funct_1(k2_funct_1(sK4)),sK4) | ~v2_funct_1(k2_funct_1(sK4)) | u1_struct_0(sK2) != k2_relset_1(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)) | ~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK2)))) | (~spl5_1 | spl5_4 | ~spl5_13)),
% 0.22/0.50    inference(subsumption_resolution,[],[f444,f176])).
% 0.22/0.50  fof(f176,plain,(
% 0.22/0.50    v1_funct_1(k2_funct_1(sK4)) | ~spl5_1),
% 0.22/0.50    inference(resolution,[],[f143,f58])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | v1_funct_1(k2_funct_1(X2))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f37])).
% 0.22/0.50  fof(f444,plain,(
% 0.22/0.50    ~r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_funct_1(k2_funct_1(sK4)),sK4) | ~v2_funct_1(k2_funct_1(sK4)) | u1_struct_0(sK2) != k2_relset_1(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)) | ~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_1(k2_funct_1(sK4)) | (spl5_4 | ~spl5_13)),
% 0.22/0.50    inference(subsumption_resolution,[],[f441,f421])).
% 0.22/0.50  fof(f421,plain,(
% 0.22/0.50    v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),u1_struct_0(sK2)) | ~spl5_13),
% 0.22/0.50    inference(subsumption_resolution,[],[f420,f42])).
% 0.22/0.50  fof(f420,plain,(
% 0.22/0.50    v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(sK4) | ~spl5_13),
% 0.22/0.50    inference(subsumption_resolution,[],[f419,f82])).
% 0.22/0.50  fof(f419,plain,(
% 0.22/0.50    v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4) | ~spl5_13),
% 0.22/0.50    inference(subsumption_resolution,[],[f418,f81])).
% 0.22/0.50  fof(f418,plain,(
% 0.22/0.50    v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),u1_struct_0(sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4) | ~spl5_13),
% 0.22/0.50    inference(subsumption_resolution,[],[f417,f80])).
% 0.22/0.50  fof(f417,plain,(
% 0.22/0.50    v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),u1_struct_0(sK2)) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4) | ~spl5_13),
% 0.22/0.50    inference(subsumption_resolution,[],[f415,f46])).
% 0.22/0.50  fof(f415,plain,(
% 0.22/0.50    v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),u1_struct_0(sK2)) | ~v2_funct_1(sK4) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4) | ~spl5_13),
% 0.22/0.50    inference(superposition,[],[f245,f62])).
% 0.22/0.50  fof(f245,plain,(
% 0.22/0.50    v1_funct_2(k2_tops_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4),k2_struct_0(sK3),u1_struct_0(sK2)) | ~spl5_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f244])).
% 0.22/0.50  fof(f441,plain,(
% 0.22/0.50    ~r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_funct_1(k2_funct_1(sK4)),sK4) | ~v2_funct_1(k2_funct_1(sK4)) | u1_struct_0(sK2) != k2_relset_1(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)) | ~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(k2_funct_1(sK4)) | spl5_4),
% 0.22/0.50    inference(superposition,[],[f201,f62])).
% 0.22/0.50  fof(f201,plain,(
% 0.22/0.50    ~r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4) | spl5_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f199])).
% 0.22/0.50  fof(f409,plain,(
% 0.22/0.50    ~spl5_1 | spl5_13),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f408])).
% 0.22/0.50  fof(f408,plain,(
% 0.22/0.50    $false | (~spl5_1 | spl5_13)),
% 0.22/0.50    inference(subsumption_resolution,[],[f406,f143])).
% 0.22/0.50  fof(f406,plain,(
% 0.22/0.50    ~sP1(u1_struct_0(sK2),k2_struct_0(sK3),sK4) | spl5_13),
% 0.22/0.50    inference(resolution,[],[f403,f59])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | ~sP1(X0,X1,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f37])).
% 0.22/0.50  fof(f403,plain,(
% 0.22/0.50    ~v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),u1_struct_0(sK2)) | spl5_13),
% 0.22/0.50    inference(subsumption_resolution,[],[f402,f42])).
% 0.22/0.50  fof(f402,plain,(
% 0.22/0.50    ~v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(sK4) | spl5_13),
% 0.22/0.50    inference(subsumption_resolution,[],[f401,f82])).
% 0.22/0.50  fof(f401,plain,(
% 0.22/0.50    ~v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4) | spl5_13),
% 0.22/0.50    inference(subsumption_resolution,[],[f400,f81])).
% 0.22/0.50  fof(f400,plain,(
% 0.22/0.50    ~v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),u1_struct_0(sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4) | spl5_13),
% 0.22/0.50    inference(subsumption_resolution,[],[f399,f80])).
% 0.22/0.50  fof(f399,plain,(
% 0.22/0.50    ~v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),u1_struct_0(sK2)) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4) | spl5_13),
% 0.22/0.50    inference(subsumption_resolution,[],[f397,f46])).
% 0.22/0.50  fof(f397,plain,(
% 0.22/0.50    ~v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),u1_struct_0(sK2)) | ~v2_funct_1(sK4) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4) | spl5_13),
% 0.22/0.50    inference(superposition,[],[f246,f62])).
% 0.22/0.50  fof(f246,plain,(
% 0.22/0.50    ~v1_funct_2(k2_tops_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4),k2_struct_0(sK3),u1_struct_0(sK2)) | spl5_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f244])).
% 0.22/0.50  fof(f360,plain,(
% 0.22/0.50    spl5_2),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f359])).
% 0.22/0.50  fof(f359,plain,(
% 0.22/0.50    $false | spl5_2),
% 0.22/0.50    inference(subsumption_resolution,[],[f358,f41])).
% 0.22/0.50  fof(f358,plain,(
% 0.22/0.50    ~l1_struct_0(sK3) | spl5_2),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f357])).
% 0.22/0.50  fof(f357,plain,(
% 0.22/0.50    k2_struct_0(sK3) != k2_struct_0(sK3) | ~l1_struct_0(sK3) | spl5_2),
% 0.22/0.50    inference(superposition,[],[f147,f48])).
% 0.22/0.50  fof(f147,plain,(
% 0.22/0.50    u1_struct_0(sK3) != k2_struct_0(sK3) | spl5_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f145])).
% 0.22/0.50  fof(f294,plain,(
% 0.22/0.50    ~spl5_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f293,f199])).
% 0.22/0.50  fof(f293,plain,(
% 0.22/0.50    ~r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f292,f42])).
% 0.22/0.50  fof(f292,plain,(
% 0.22/0.50    ~r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4) | ~v1_funct_1(sK4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f291,f82])).
% 0.22/0.50  fof(f291,plain,(
% 0.22/0.50    ~r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4) | ~v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f290,f81])).
% 0.22/0.50  fof(f290,plain,(
% 0.22/0.50    ~r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f289,f80])).
% 0.22/0.50  fof(f289,plain,(
% 0.22/0.50    ~r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f189,f46])).
% 0.22/0.50  fof(f189,plain,(
% 0.22/0.50    ~r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4) | ~v2_funct_1(sK4) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 0.22/0.50    inference(superposition,[],[f79,f62])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    ~r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4)),sK4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f71,f41])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    ~r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4)),sK4) | ~l1_struct_0(sK3)),
% 0.22/0.50    inference(superposition,[],[f47,f48])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK4)),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f163,plain,(
% 0.22/0.50    spl5_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f162,f141])).
% 0.22/0.50  fof(f162,plain,(
% 0.22/0.50    sP1(u1_struct_0(sK2),k2_struct_0(sK3),sK4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f161,f42])).
% 0.22/0.50  fof(f161,plain,(
% 0.22/0.50    sP1(u1_struct_0(sK2),k2_struct_0(sK3),sK4) | ~v1_funct_1(sK4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f160,f82])).
% 0.22/0.50  fof(f160,plain,(
% 0.22/0.50    sP1(u1_struct_0(sK2),k2_struct_0(sK3),sK4) | ~v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f159,f46])).
% 0.22/0.50  fof(f159,plain,(
% 0.22/0.50    ~v2_funct_1(sK4) | sP1(u1_struct_0(sK2),k2_struct_0(sK3),sK4) | ~v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f132,f80])).
% 0.22/0.50  fof(f132,plain,(
% 0.22/0.50    k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4) | ~v2_funct_1(sK4) | sP1(u1_struct_0(sK2),k2_struct_0(sK3),sK4) | ~v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 0.22/0.50    inference(resolution,[],[f61,f81])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | sP1(X0,X1,X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (sP1(X0,X1,X2) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.50    inference(definition_folding,[],[f23,f30])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.50    inference(flattening,[],[f22])).
% 0.22/0.50  % (4852)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (4840)------------------------------
% 0.22/0.50  % (4840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (4840)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (4840)Memory used [KB]: 6524
% 0.22/0.50  % (4840)Time elapsed: 0.084 s
% 0.22/0.50  % (4840)------------------------------
% 0.22/0.50  % (4840)------------------------------
% 0.22/0.50  % (4833)Success in time 0.142 s
%------------------------------------------------------------------------------
