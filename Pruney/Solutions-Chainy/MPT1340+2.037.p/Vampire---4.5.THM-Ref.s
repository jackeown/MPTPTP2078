%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 931 expanded)
%              Number of leaves         :   25 ( 345 expanded)
%              Depth                    :   20
%              Number of atoms          :  722 (7300 expanded)
%              Number of equality atoms :   97 ( 951 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f863,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f225,f325,f352,f356,f412,f462,f473,f506,f562,f574,f783,f862])).

fof(f862,plain,
    ( ~ spl5_2
    | spl5_30
    | ~ spl5_41 ),
    inference(avatar_contradiction_clause,[],[f861])).

fof(f861,plain,
    ( $false
    | ~ spl5_2
    | spl5_30
    | ~ spl5_41 ),
    inference(subsumption_resolution,[],[f766,f777])).

fof(f777,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2)
    | ~ spl5_41 ),
    inference(avatar_component_clause,[],[f776])).

fof(f776,plain,
    ( spl5_41
  <=> u1_struct_0(sK2) = k2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f766,plain,
    ( u1_struct_0(sK2) != k2_struct_0(sK2)
    | ~ spl5_2
    | spl5_30 ),
    inference(subsumption_resolution,[],[f765,f38])).

fof(f38,plain,(
    l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK4)
    & v2_funct_1(sK4)
    & k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK4)
    & l1_struct_0(sK3)
    & ~ v2_struct_0(sK3)
    & l1_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f12,f33,f32,f31])).

fof(f31,plain,
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

fof(f32,plain,
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

fof(f33,plain,
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).

fof(f765,plain,
    ( u1_struct_0(sK2) != k2_struct_0(sK2)
    | ~ l1_struct_0(sK2)
    | ~ spl5_2
    | spl5_30 ),
    inference(subsumption_resolution,[],[f764,f41])).

fof(f41,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f764,plain,
    ( u1_struct_0(sK2) != k2_struct_0(sK2)
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK2)
    | ~ spl5_2
    | spl5_30 ),
    inference(subsumption_resolution,[],[f763,f80])).

fof(f80,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f72,f40])).

fof(f40,plain,(
    l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f72,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))
    | ~ l1_struct_0(sK3) ),
    inference(superposition,[],[f42,f47])).

fof(f47,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f42,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f34])).

fof(f763,plain,
    ( u1_struct_0(sK2) != k2_struct_0(sK2)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK2)
    | ~ spl5_2
    | spl5_30 ),
    inference(subsumption_resolution,[],[f762,f79])).

fof(f79,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3)))) ),
    inference(subsumption_resolution,[],[f71,f40])).

fof(f71,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3))))
    | ~ l1_struct_0(sK3) ),
    inference(superposition,[],[f43,f47])).

fof(f43,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f34])).

fof(f762,plain,
    ( u1_struct_0(sK2) != k2_struct_0(sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK2)
    | ~ spl5_2
    | spl5_30 ),
    inference(subsumption_resolution,[],[f761,f78])).

fof(f78,plain,(
    k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4) ),
    inference(subsumption_resolution,[],[f70,f40])).

fof(f70,plain,
    ( k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ l1_struct_0(sK3) ),
    inference(superposition,[],[f44,f47])).

fof(f44,plain,(
    k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f761,plain,
    ( u1_struct_0(sK2) != k2_struct_0(sK2)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK2)
    | ~ spl5_2
    | spl5_30 ),
    inference(subsumption_resolution,[],[f757,f45])).

fof(f45,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f757,plain,
    ( u1_struct_0(sK2) != k2_struct_0(sK2)
    | ~ v2_funct_1(sK4)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK2)
    | ~ spl5_2
    | spl5_30 ),
    inference(superposition,[],[f453,f752])).

fof(f752,plain,
    ( ! [X4,X3] :
        ( k2_struct_0(X3) = k2_relset_1(k2_struct_0(sK3),u1_struct_0(X3),k2_funct_1(X4))
        | ~ v2_funct_1(X4)
        | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(X3),k2_struct_0(sK3),X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK3))))
        | ~ v1_funct_2(X4,u1_struct_0(X3),k2_struct_0(sK3))
        | ~ v1_funct_1(X4)
        | ~ l1_struct_0(X3) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f751,f39])).

fof(f39,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f751,plain,
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
    inference(subsumption_resolution,[],[f745,f40])).

fof(f745,plain,
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
    inference(superposition,[],[f407,f167])).

fof(f167,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl5_2
  <=> u1_struct_0(sK3) = k2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f407,plain,(
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
    inference(subsumption_resolution,[],[f406,f47])).

fof(f406,plain,(
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
    inference(inner_rewriting,[],[f400])).

fof(f400,plain,(
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
    inference(duplicate_literal_removal,[],[f399])).

fof(f399,plain,(
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
    inference(superposition,[],[f49,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f49,plain,(
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
    inference(cnf_transformation,[],[f15])).

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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).

fof(f453,plain,
    ( u1_struct_0(sK2) != k2_relset_1(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4))
    | spl5_30 ),
    inference(avatar_component_clause,[],[f451])).

fof(f451,plain,
    ( spl5_30
  <=> u1_struct_0(sK2) = k2_relset_1(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f783,plain,(
    spl5_41 ),
    inference(avatar_contradiction_clause,[],[f782])).

fof(f782,plain,
    ( $false
    | spl5_41 ),
    inference(subsumption_resolution,[],[f781,f38])).

fof(f781,plain,
    ( ~ l1_struct_0(sK2)
    | spl5_41 ),
    inference(trivial_inequality_removal,[],[f780])).

fof(f780,plain,
    ( k2_struct_0(sK2) != k2_struct_0(sK2)
    | ~ l1_struct_0(sK2)
    | spl5_41 ),
    inference(superposition,[],[f778,f47])).

fof(f778,plain,
    ( u1_struct_0(sK2) != k2_struct_0(sK2)
    | spl5_41 ),
    inference(avatar_component_clause,[],[f776])).

fof(f574,plain,(
    spl5_31 ),
    inference(avatar_contradiction_clause,[],[f573])).

fof(f573,plain,
    ( $false
    | spl5_31 ),
    inference(subsumption_resolution,[],[f572,f89])).

fof(f89,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f55,f43])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f572,plain,
    ( ~ v1_relat_1(sK4)
    | spl5_31 ),
    inference(subsumption_resolution,[],[f571,f41])).

fof(f571,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | spl5_31 ),
    inference(subsumption_resolution,[],[f570,f45])).

fof(f570,plain,
    ( ~ v2_funct_1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | spl5_31 ),
    inference(resolution,[],[f567,f53])).

fof(f53,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f17,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ sP0(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f17,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f567,plain,
    ( ~ sP0(sK4)
    | spl5_31 ),
    inference(resolution,[],[f457,f52])).

fof(f52,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f457,plain,
    ( ~ v2_funct_1(k2_funct_1(sK4))
    | spl5_31 ),
    inference(avatar_component_clause,[],[f455])).

fof(f455,plain,
    ( spl5_31
  <=> v2_funct_1(k2_funct_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f562,plain,(
    spl5_32 ),
    inference(avatar_contradiction_clause,[],[f561])).

fof(f561,plain,
    ( $false
    | spl5_32 ),
    inference(subsumption_resolution,[],[f560,f89])).

fof(f560,plain,
    ( ~ v1_relat_1(sK4)
    | spl5_32 ),
    inference(subsumption_resolution,[],[f559,f41])).

fof(f559,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | spl5_32 ),
    inference(subsumption_resolution,[],[f558,f45])).

fof(f558,plain,
    ( ~ v2_funct_1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | spl5_32 ),
    inference(subsumption_resolution,[],[f555,f136])).

fof(f136,plain,(
    r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4,sK4) ),
    inference(subsumption_resolution,[],[f135,f41])).

fof(f135,plain,
    ( r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4,sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f128,f80])).

fof(f128,plain,
    ( r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4,sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f64,f79])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f26])).

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
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f555,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4,sK4)
    | ~ v2_funct_1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | spl5_32 ),
    inference(superposition,[],[f461,f54])).

fof(f54,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(f461,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_funct_1(k2_funct_1(sK4)),sK4)
    | spl5_32 ),
    inference(avatar_component_clause,[],[f459])).

fof(f459,plain,
    ( spl5_32
  <=> r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_funct_1(k2_funct_1(sK4)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f506,plain,
    ( spl5_29
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f505,f250,f447])).

fof(f447,plain,
    ( spl5_29
  <=> m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f250,plain,
    ( spl5_18
  <=> m1_subset_1(k2_tops_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f505,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK2))))
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f504,f41])).

fof(f504,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_1(sK4)
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f503,f80])).

fof(f503,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f502,f79])).

fof(f502,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f501,f78])).

fof(f501,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK2))))
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f484,f45])).

fof(f484,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v2_funct_1(sK4)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ spl5_18 ),
    inference(superposition,[],[f251,f60])).

fof(f251,plain,
    ( m1_subset_1(k2_tops_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK2))))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f250])).

fof(f473,plain,(
    spl5_18 ),
    inference(avatar_contradiction_clause,[],[f472])).

fof(f472,plain,
    ( $false
    | spl5_18 ),
    inference(subsumption_resolution,[],[f469,f115])).

fof(f115,plain,(
    sP1(u1_struct_0(sK2),k2_struct_0(sK3),sK4) ),
    inference(subsumption_resolution,[],[f114,f41])).

fof(f114,plain,
    ( sP1(u1_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f107,f80])).

fof(f107,plain,
    ( sP1(u1_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f59,f79])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP1(X0,X1,X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f22,f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ sP1(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f469,plain,
    ( ~ sP1(u1_struct_0(sK2),k2_struct_0(sK3),sK4)
    | spl5_18 ),
    inference(resolution,[],[f252,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f252,plain,
    ( ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK2))))
    | spl5_18 ),
    inference(avatar_component_clause,[],[f250])).

fof(f462,plain,
    ( ~ spl5_29
    | ~ spl5_30
    | ~ spl5_31
    | ~ spl5_32
    | spl5_1
    | ~ spl5_17
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f445,f336,f246,f162,f459,f455,f451,f447])).

fof(f162,plain,
    ( spl5_1
  <=> r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f246,plain,
    ( spl5_17
  <=> v1_funct_2(k2_tops_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4),k2_struct_0(sK3),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f336,plain,
    ( spl5_28
  <=> v1_funct_1(k2_funct_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f445,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_funct_1(k2_funct_1(sK4)),sK4)
    | ~ v2_funct_1(k2_funct_1(sK4))
    | u1_struct_0(sK2) != k2_relset_1(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4))
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK2))))
    | spl5_1
    | ~ spl5_17
    | ~ spl5_28 ),
    inference(subsumption_resolution,[],[f444,f337])).

fof(f337,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f336])).

fof(f444,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_funct_1(k2_funct_1(sK4)),sK4)
    | ~ v2_funct_1(k2_funct_1(sK4))
    | u1_struct_0(sK2) != k2_relset_1(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4))
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | spl5_1
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f441,f430])).

fof(f430,plain,
    ( v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),u1_struct_0(sK2))
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f429,f41])).

fof(f429,plain,
    ( v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_1(sK4)
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f428,f80])).

fof(f428,plain,
    ( v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f427,f79])).

fof(f427,plain,
    ( v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f426,f78])).

fof(f426,plain,
    ( v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),u1_struct_0(sK2))
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f424,f45])).

fof(f424,plain,
    ( v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),u1_struct_0(sK2))
    | ~ v2_funct_1(sK4)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ spl5_17 ),
    inference(superposition,[],[f247,f60])).

fof(f247,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4),k2_struct_0(sK3),u1_struct_0(sK2))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f246])).

fof(f441,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_funct_1(k2_funct_1(sK4)),sK4)
    | ~ v2_funct_1(k2_funct_1(sK4))
    | u1_struct_0(sK2) != k2_relset_1(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4))
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | spl5_1 ),
    inference(superposition,[],[f164,f60])).

fof(f164,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f162])).

fof(f412,plain,(
    spl5_17 ),
    inference(avatar_contradiction_clause,[],[f411])).

fof(f411,plain,
    ( $false
    | spl5_17 ),
    inference(subsumption_resolution,[],[f408,f115])).

fof(f408,plain,
    ( ~ sP1(u1_struct_0(sK2),k2_struct_0(sK3),sK4)
    | spl5_17 ),
    inference(resolution,[],[f248,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f248,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4),k2_struct_0(sK3),u1_struct_0(sK2))
    | spl5_17 ),
    inference(avatar_component_clause,[],[f246])).

fof(f356,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f355])).

fof(f355,plain,
    ( $false
    | spl5_2 ),
    inference(subsumption_resolution,[],[f354,f40])).

fof(f354,plain,
    ( ~ l1_struct_0(sK3)
    | spl5_2 ),
    inference(trivial_inequality_removal,[],[f353])).

fof(f353,plain,
    ( k2_struct_0(sK3) != k2_struct_0(sK3)
    | ~ l1_struct_0(sK3)
    | spl5_2 ),
    inference(superposition,[],[f168,f47])).

fof(f168,plain,
    ( u1_struct_0(sK3) != k2_struct_0(sK3)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f166])).

fof(f352,plain,
    ( spl5_28
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f351,f171,f166,f336])).

fof(f171,plain,
    ( spl5_3
  <=> v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f351,plain,
    ( u1_struct_0(sK3) != k2_struct_0(sK3)
    | v1_funct_1(k2_funct_1(sK4))
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f350,f44])).

fof(f350,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | u1_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f349,f41])).

fof(f349,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | u1_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | ~ v1_funct_1(sK4)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f348,f42])).

fof(f348,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | u1_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f347,f43])).

fof(f347,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | u1_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f342,f45])).

fof(f342,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ v2_funct_1(sK4)
    | u1_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ spl5_3 ),
    inference(superposition,[],[f172,f60])).

fof(f172,plain,
    ( v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f171])).

fof(f325,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f324])).

fof(f324,plain,
    ( $false
    | spl5_3 ),
    inference(subsumption_resolution,[],[f320,f111])).

fof(f111,plain,(
    sP1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
    inference(subsumption_resolution,[],[f110,f41])).

fof(f110,plain,
    ( sP1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f105,f42])).

fof(f105,plain,
    ( sP1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f59,f43])).

fof(f320,plain,
    ( ~ sP1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | spl5_3 ),
    inference(resolution,[],[f173,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_tops_2(X0,X1,X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f173,plain,
    ( ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f171])).

fof(f225,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f224,f162])).

fof(f224,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4) ),
    inference(subsumption_resolution,[],[f223,f41])).

fof(f223,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f222,f80])).

fof(f222,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f221,f79])).

fof(f221,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f220,f78])).

fof(f220,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f146,f45])).

fof(f146,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4)
    | ~ v2_funct_1(sK4)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(superposition,[],[f77,f60])).

fof(f77,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4)),sK4) ),
    inference(subsumption_resolution,[],[f69,f40])).

fof(f69,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4)),sK4)
    | ~ l1_struct_0(sK3) ),
    inference(superposition,[],[f46,f47])).

fof(f46,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK4) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:39:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (10282)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.46  % (10291)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (10297)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.48  % (10282)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f863,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f225,f325,f352,f356,f412,f462,f473,f506,f562,f574,f783,f862])).
% 0.20/0.48  fof(f862,plain,(
% 0.20/0.48    ~spl5_2 | spl5_30 | ~spl5_41),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f861])).
% 0.20/0.48  fof(f861,plain,(
% 0.20/0.48    $false | (~spl5_2 | spl5_30 | ~spl5_41)),
% 0.20/0.48    inference(subsumption_resolution,[],[f766,f777])).
% 0.20/0.48  fof(f777,plain,(
% 0.20/0.48    u1_struct_0(sK2) = k2_struct_0(sK2) | ~spl5_41),
% 0.20/0.48    inference(avatar_component_clause,[],[f776])).
% 0.20/0.48  fof(f776,plain,(
% 0.20/0.48    spl5_41 <=> u1_struct_0(sK2) = k2_struct_0(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 0.20/0.48  fof(f766,plain,(
% 0.20/0.48    u1_struct_0(sK2) != k2_struct_0(sK2) | (~spl5_2 | spl5_30)),
% 0.20/0.48    inference(subsumption_resolution,[],[f765,f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    l1_struct_0(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK4) & v2_funct_1(sK4) & k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & l1_struct_0(sK3) & ~v2_struct_0(sK3)) & l1_struct_0(sK2)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f12,f33,f32,f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK2))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X2) = k2_struct_0(sK3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X2)) & l1_struct_0(sK3) & ~v2_struct_0(sK3))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ? [X2] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X2) = k2_struct_0(sK3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK4) & v2_funct_1(sK4) & k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,negated_conjecture,(
% 0.20/0.48    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.20/0.48    inference(negated_conjecture,[],[f9])).
% 0.20/0.48  fof(f9,conjecture,(
% 0.20/0.48    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).
% 0.20/0.48  fof(f765,plain,(
% 0.20/0.48    u1_struct_0(sK2) != k2_struct_0(sK2) | ~l1_struct_0(sK2) | (~spl5_2 | spl5_30)),
% 0.20/0.48    inference(subsumption_resolution,[],[f764,f41])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    v1_funct_1(sK4)),
% 0.20/0.48    inference(cnf_transformation,[],[f34])).
% 0.20/0.48  fof(f764,plain,(
% 0.20/0.48    u1_struct_0(sK2) != k2_struct_0(sK2) | ~v1_funct_1(sK4) | ~l1_struct_0(sK2) | (~spl5_2 | spl5_30)),
% 0.20/0.48    inference(subsumption_resolution,[],[f763,f80])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3))),
% 0.20/0.48    inference(subsumption_resolution,[],[f72,f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    l1_struct_0(sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f34])).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) | ~l1_struct_0(sK3)),
% 0.20/0.48    inference(superposition,[],[f42,f47])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.20/0.48    inference(cnf_transformation,[],[f34])).
% 0.20/0.48  fof(f763,plain,(
% 0.20/0.48    u1_struct_0(sK2) != k2_struct_0(sK2) | ~v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK2) | (~spl5_2 | spl5_30)),
% 0.20/0.48    inference(subsumption_resolution,[],[f762,f79])).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3))))),
% 0.20/0.48    inference(subsumption_resolution,[],[f71,f40])).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3)))) | ~l1_struct_0(sK3)),
% 0.20/0.48    inference(superposition,[],[f43,f47])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 0.20/0.48    inference(cnf_transformation,[],[f34])).
% 0.20/0.48  fof(f762,plain,(
% 0.20/0.48    u1_struct_0(sK2) != k2_struct_0(sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK2) | (~spl5_2 | spl5_30)),
% 0.20/0.48    inference(subsumption_resolution,[],[f761,f78])).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4)),
% 0.20/0.48    inference(subsumption_resolution,[],[f70,f40])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4) | ~l1_struct_0(sK3)),
% 0.20/0.48    inference(superposition,[],[f44,f47])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),
% 0.20/0.48    inference(cnf_transformation,[],[f34])).
% 0.20/0.48  fof(f761,plain,(
% 0.20/0.48    u1_struct_0(sK2) != k2_struct_0(sK2) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK2) | (~spl5_2 | spl5_30)),
% 0.20/0.48    inference(subsumption_resolution,[],[f757,f45])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    v2_funct_1(sK4)),
% 0.20/0.48    inference(cnf_transformation,[],[f34])).
% 0.20/0.48  fof(f757,plain,(
% 0.20/0.48    u1_struct_0(sK2) != k2_struct_0(sK2) | ~v2_funct_1(sK4) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK2) | (~spl5_2 | spl5_30)),
% 0.20/0.48    inference(superposition,[],[f453,f752])).
% 0.20/0.48  fof(f752,plain,(
% 0.20/0.48    ( ! [X4,X3] : (k2_struct_0(X3) = k2_relset_1(k2_struct_0(sK3),u1_struct_0(X3),k2_funct_1(X4)) | ~v2_funct_1(X4) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(X3),k2_struct_0(sK3),X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK3)))) | ~v1_funct_2(X4,u1_struct_0(X3),k2_struct_0(sK3)) | ~v1_funct_1(X4) | ~l1_struct_0(X3)) ) | ~spl5_2),
% 0.20/0.48    inference(subsumption_resolution,[],[f751,f39])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ~v2_struct_0(sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f34])).
% 0.20/0.49  fof(f751,plain,(
% 0.20/0.49    ( ! [X4,X3] : (k2_struct_0(X3) = k2_relset_1(k2_struct_0(sK3),u1_struct_0(X3),k2_funct_1(X4)) | ~v2_funct_1(X4) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(X3),k2_struct_0(sK3),X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK3)))) | ~v1_funct_2(X4,u1_struct_0(X3),k2_struct_0(sK3)) | ~v1_funct_1(X4) | v2_struct_0(sK3) | ~l1_struct_0(X3)) ) | ~spl5_2),
% 0.20/0.49    inference(subsumption_resolution,[],[f745,f40])).
% 0.20/0.49  fof(f745,plain,(
% 0.20/0.49    ( ! [X4,X3] : (k2_struct_0(X3) = k2_relset_1(k2_struct_0(sK3),u1_struct_0(X3),k2_funct_1(X4)) | ~v2_funct_1(X4) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(X3),k2_struct_0(sK3),X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK3)))) | ~v1_funct_2(X4,u1_struct_0(X3),k2_struct_0(sK3)) | ~v1_funct_1(X4) | ~l1_struct_0(sK3) | v2_struct_0(sK3) | ~l1_struct_0(X3)) ) | ~spl5_2),
% 0.20/0.49    inference(superposition,[],[f407,f167])).
% 0.20/0.49  fof(f167,plain,(
% 0.20/0.49    u1_struct_0(sK3) = k2_struct_0(sK3) | ~spl5_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f166])).
% 0.20/0.49  fof(f166,plain,(
% 0.20/0.49    spl5_2 <=> u1_struct_0(sK3) = k2_struct_0(sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.49  fof(f407,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_funct_1(X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f406,f47])).
% 0.20/0.49  fof(f406,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_funct_1(X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | u1_struct_0(X1) != k2_struct_0(X1)) )),
% 0.20/0.49    inference(inner_rewriting,[],[f400])).
% 0.20/0.49  fof(f400,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_funct_1(X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | u1_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f399])).
% 0.20/0.49  fof(f399,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_funct_1(X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | ~v2_funct_1(X2) | u1_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) )),
% 0.20/0.49    inference(superposition,[],[f49,f60])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.49    inference(flattening,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_tops_2(X0,X1,X2) = k2_funct_1(X2)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : ((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_struct_0(X1) | v2_struct_0(X1))) | ~l1_struct_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).
% 0.20/0.49  fof(f453,plain,(
% 0.20/0.49    u1_struct_0(sK2) != k2_relset_1(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)) | spl5_30),
% 0.20/0.49    inference(avatar_component_clause,[],[f451])).
% 0.20/0.49  fof(f451,plain,(
% 0.20/0.49    spl5_30 <=> u1_struct_0(sK2) = k2_relset_1(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.20/0.49  fof(f783,plain,(
% 0.20/0.49    spl5_41),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f782])).
% 0.20/0.49  fof(f782,plain,(
% 0.20/0.49    $false | spl5_41),
% 0.20/0.49    inference(subsumption_resolution,[],[f781,f38])).
% 0.20/0.49  fof(f781,plain,(
% 0.20/0.49    ~l1_struct_0(sK2) | spl5_41),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f780])).
% 0.20/0.49  fof(f780,plain,(
% 0.20/0.49    k2_struct_0(sK2) != k2_struct_0(sK2) | ~l1_struct_0(sK2) | spl5_41),
% 0.20/0.49    inference(superposition,[],[f778,f47])).
% 0.20/0.49  fof(f778,plain,(
% 0.20/0.49    u1_struct_0(sK2) != k2_struct_0(sK2) | spl5_41),
% 0.20/0.49    inference(avatar_component_clause,[],[f776])).
% 0.20/0.49  fof(f574,plain,(
% 0.20/0.49    spl5_31),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f573])).
% 0.20/0.49  fof(f573,plain,(
% 0.20/0.49    $false | spl5_31),
% 0.20/0.49    inference(subsumption_resolution,[],[f572,f89])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    v1_relat_1(sK4)),
% 0.20/0.49    inference(resolution,[],[f55,f43])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.49  fof(f572,plain,(
% 0.20/0.49    ~v1_relat_1(sK4) | spl5_31),
% 0.20/0.49    inference(subsumption_resolution,[],[f571,f41])).
% 0.20/0.49  fof(f571,plain,(
% 0.20/0.49    ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | spl5_31),
% 0.20/0.49    inference(subsumption_resolution,[],[f570,f45])).
% 0.20/0.49  fof(f570,plain,(
% 0.20/0.49    ~v2_funct_1(sK4) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | spl5_31),
% 0.20/0.49    inference(resolution,[],[f567,f53])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ( ! [X0] : (sP0(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0] : (sP0(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(definition_folding,[],[f17,f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~sP0(X0))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(flattening,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).
% 0.20/0.49  fof(f567,plain,(
% 0.20/0.49    ~sP0(sK4) | spl5_31),
% 0.20/0.49    inference(resolution,[],[f457,f52])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~sP0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~sP0(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f27])).
% 0.20/0.49  fof(f457,plain,(
% 0.20/0.49    ~v2_funct_1(k2_funct_1(sK4)) | spl5_31),
% 0.20/0.49    inference(avatar_component_clause,[],[f455])).
% 0.20/0.49  fof(f455,plain,(
% 0.20/0.49    spl5_31 <=> v2_funct_1(k2_funct_1(sK4))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 0.20/0.49  fof(f562,plain,(
% 0.20/0.49    spl5_32),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f561])).
% 0.20/0.49  fof(f561,plain,(
% 0.20/0.49    $false | spl5_32),
% 0.20/0.49    inference(subsumption_resolution,[],[f560,f89])).
% 0.20/0.49  fof(f560,plain,(
% 0.20/0.49    ~v1_relat_1(sK4) | spl5_32),
% 0.20/0.49    inference(subsumption_resolution,[],[f559,f41])).
% 0.20/0.49  fof(f559,plain,(
% 0.20/0.49    ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | spl5_32),
% 0.20/0.49    inference(subsumption_resolution,[],[f558,f45])).
% 0.20/0.49  fof(f558,plain,(
% 0.20/0.49    ~v2_funct_1(sK4) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | spl5_32),
% 0.20/0.49    inference(subsumption_resolution,[],[f555,f136])).
% 0.20/0.49  fof(f136,plain,(
% 0.20/0.49    r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4,sK4)),
% 0.20/0.49    inference(subsumption_resolution,[],[f135,f41])).
% 0.20/0.49  fof(f135,plain,(
% 0.20/0.49    r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4,sK4) | ~v1_funct_1(sK4)),
% 0.20/0.49    inference(subsumption_resolution,[],[f128,f80])).
% 0.20/0.49  fof(f128,plain,(
% 0.20/0.49    r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4,sK4) | ~v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 0.20/0.49    inference(resolution,[],[f64,f79])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X3,X3) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f63])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.20/0.49    inference(equality_resolution,[],[f62])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.49    inference(nnf_transformation,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.49    inference(flattening,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 0.20/0.49  fof(f555,plain,(
% 0.20/0.49    ~r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4,sK4) | ~v2_funct_1(sK4) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | spl5_32),
% 0.20/0.49    inference(superposition,[],[f461,f54])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(flattening,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
% 0.20/0.49  fof(f461,plain,(
% 0.20/0.49    ~r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_funct_1(k2_funct_1(sK4)),sK4) | spl5_32),
% 0.20/0.49    inference(avatar_component_clause,[],[f459])).
% 0.20/0.49  fof(f459,plain,(
% 0.20/0.49    spl5_32 <=> r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_funct_1(k2_funct_1(sK4)),sK4)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 0.20/0.49  fof(f506,plain,(
% 0.20/0.49    spl5_29 | ~spl5_18),
% 0.20/0.49    inference(avatar_split_clause,[],[f505,f250,f447])).
% 0.20/0.49  fof(f447,plain,(
% 0.20/0.49    spl5_29 <=> m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK2))))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 0.20/0.49  fof(f250,plain,(
% 0.20/0.49    spl5_18 <=> m1_subset_1(k2_tops_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK2))))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.20/0.49  fof(f505,plain,(
% 0.20/0.49    m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK2)))) | ~spl5_18),
% 0.20/0.49    inference(subsumption_resolution,[],[f504,f41])).
% 0.20/0.49  fof(f504,plain,(
% 0.20/0.49    m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_1(sK4) | ~spl5_18),
% 0.20/0.49    inference(subsumption_resolution,[],[f503,f80])).
% 0.20/0.49  fof(f503,plain,(
% 0.20/0.49    m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4) | ~spl5_18),
% 0.20/0.49    inference(subsumption_resolution,[],[f502,f79])).
% 0.20/0.49  fof(f502,plain,(
% 0.20/0.49    m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK2)))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4) | ~spl5_18),
% 0.20/0.49    inference(subsumption_resolution,[],[f501,f78])).
% 0.20/0.49  fof(f501,plain,(
% 0.20/0.49    m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK2)))) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4) | ~spl5_18),
% 0.20/0.49    inference(subsumption_resolution,[],[f484,f45])).
% 0.20/0.49  fof(f484,plain,(
% 0.20/0.49    m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK2)))) | ~v2_funct_1(sK4) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4) | ~spl5_18),
% 0.20/0.49    inference(superposition,[],[f251,f60])).
% 0.20/0.49  fof(f251,plain,(
% 0.20/0.49    m1_subset_1(k2_tops_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK2)))) | ~spl5_18),
% 0.20/0.49    inference(avatar_component_clause,[],[f250])).
% 0.20/0.49  fof(f473,plain,(
% 0.20/0.49    spl5_18),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f472])).
% 0.20/0.49  fof(f472,plain,(
% 0.20/0.49    $false | spl5_18),
% 0.20/0.49    inference(subsumption_resolution,[],[f469,f115])).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    sP1(u1_struct_0(sK2),k2_struct_0(sK3),sK4)),
% 0.20/0.49    inference(subsumption_resolution,[],[f114,f41])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    sP1(u1_struct_0(sK2),k2_struct_0(sK3),sK4) | ~v1_funct_1(sK4)),
% 0.20/0.49    inference(subsumption_resolution,[],[f107,f80])).
% 0.20/0.49  fof(f107,plain,(
% 0.20/0.49    sP1(u1_struct_0(sK2),k2_struct_0(sK3),sK4) | ~v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 0.20/0.49    inference(resolution,[],[f59,f79])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP1(X0,X1,X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (sP1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.49    inference(definition_folding,[],[f22,f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~sP1(X0,X1,X2))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.49    inference(flattening,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).
% 0.20/0.49  fof(f469,plain,(
% 0.20/0.49    ~sP1(u1_struct_0(sK2),k2_struct_0(sK3),sK4) | spl5_18),
% 0.20/0.49    inference(resolution,[],[f252,f58])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~sP1(X0,X1,X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~sP1(X0,X1,X2))),
% 0.20/0.49    inference(nnf_transformation,[],[f29])).
% 0.20/0.49  fof(f252,plain,(
% 0.20/0.49    ~m1_subset_1(k2_tops_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK2)))) | spl5_18),
% 0.20/0.49    inference(avatar_component_clause,[],[f250])).
% 0.20/0.49  fof(f462,plain,(
% 0.20/0.49    ~spl5_29 | ~spl5_30 | ~spl5_31 | ~spl5_32 | spl5_1 | ~spl5_17 | ~spl5_28),
% 0.20/0.49    inference(avatar_split_clause,[],[f445,f336,f246,f162,f459,f455,f451,f447])).
% 0.20/0.49  fof(f162,plain,(
% 0.20/0.49    spl5_1 <=> r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.49  fof(f246,plain,(
% 0.20/0.49    spl5_17 <=> v1_funct_2(k2_tops_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4),k2_struct_0(sK3),u1_struct_0(sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.20/0.49  fof(f336,plain,(
% 0.20/0.49    spl5_28 <=> v1_funct_1(k2_funct_1(sK4))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 0.20/0.49  fof(f445,plain,(
% 0.20/0.49    ~r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_funct_1(k2_funct_1(sK4)),sK4) | ~v2_funct_1(k2_funct_1(sK4)) | u1_struct_0(sK2) != k2_relset_1(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)) | ~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK2)))) | (spl5_1 | ~spl5_17 | ~spl5_28)),
% 0.20/0.49    inference(subsumption_resolution,[],[f444,f337])).
% 0.20/0.49  fof(f337,plain,(
% 0.20/0.49    v1_funct_1(k2_funct_1(sK4)) | ~spl5_28),
% 0.20/0.49    inference(avatar_component_clause,[],[f336])).
% 0.20/0.49  fof(f444,plain,(
% 0.20/0.49    ~r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_funct_1(k2_funct_1(sK4)),sK4) | ~v2_funct_1(k2_funct_1(sK4)) | u1_struct_0(sK2) != k2_relset_1(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)) | ~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_1(k2_funct_1(sK4)) | (spl5_1 | ~spl5_17)),
% 0.20/0.49    inference(subsumption_resolution,[],[f441,f430])).
% 0.20/0.49  fof(f430,plain,(
% 0.20/0.49    v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),u1_struct_0(sK2)) | ~spl5_17),
% 0.20/0.49    inference(subsumption_resolution,[],[f429,f41])).
% 0.20/0.49  fof(f429,plain,(
% 0.20/0.49    v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(sK4) | ~spl5_17),
% 0.20/0.49    inference(subsumption_resolution,[],[f428,f80])).
% 0.20/0.49  fof(f428,plain,(
% 0.20/0.49    v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4) | ~spl5_17),
% 0.20/0.49    inference(subsumption_resolution,[],[f427,f79])).
% 0.20/0.49  fof(f427,plain,(
% 0.20/0.49    v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),u1_struct_0(sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4) | ~spl5_17),
% 0.20/0.49    inference(subsumption_resolution,[],[f426,f78])).
% 0.20/0.49  fof(f426,plain,(
% 0.20/0.49    v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),u1_struct_0(sK2)) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4) | ~spl5_17),
% 0.20/0.49    inference(subsumption_resolution,[],[f424,f45])).
% 0.20/0.49  fof(f424,plain,(
% 0.20/0.49    v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),u1_struct_0(sK2)) | ~v2_funct_1(sK4) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4) | ~spl5_17),
% 0.20/0.49    inference(superposition,[],[f247,f60])).
% 0.20/0.49  fof(f247,plain,(
% 0.20/0.49    v1_funct_2(k2_tops_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4),k2_struct_0(sK3),u1_struct_0(sK2)) | ~spl5_17),
% 0.20/0.49    inference(avatar_component_clause,[],[f246])).
% 0.20/0.49  fof(f441,plain,(
% 0.20/0.49    ~r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_funct_1(k2_funct_1(sK4)),sK4) | ~v2_funct_1(k2_funct_1(sK4)) | u1_struct_0(sK2) != k2_relset_1(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)) | ~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(k2_funct_1(sK4)) | spl5_1),
% 0.20/0.49    inference(superposition,[],[f164,f60])).
% 0.20/0.49  fof(f164,plain,(
% 0.20/0.49    ~r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4) | spl5_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f162])).
% 0.20/0.49  fof(f412,plain,(
% 0.20/0.49    spl5_17),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f411])).
% 0.20/0.49  fof(f411,plain,(
% 0.20/0.49    $false | spl5_17),
% 0.20/0.49    inference(subsumption_resolution,[],[f408,f115])).
% 0.20/0.49  fof(f408,plain,(
% 0.20/0.49    ~sP1(u1_struct_0(sK2),k2_struct_0(sK3),sK4) | spl5_17),
% 0.20/0.49    inference(resolution,[],[f248,f57])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) | ~sP1(X0,X1,X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f248,plain,(
% 0.20/0.49    ~v1_funct_2(k2_tops_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4),k2_struct_0(sK3),u1_struct_0(sK2)) | spl5_17),
% 0.20/0.49    inference(avatar_component_clause,[],[f246])).
% 0.20/0.49  fof(f356,plain,(
% 0.20/0.49    spl5_2),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f355])).
% 0.20/0.49  fof(f355,plain,(
% 0.20/0.49    $false | spl5_2),
% 0.20/0.49    inference(subsumption_resolution,[],[f354,f40])).
% 0.20/0.49  fof(f354,plain,(
% 0.20/0.49    ~l1_struct_0(sK3) | spl5_2),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f353])).
% 0.20/0.49  fof(f353,plain,(
% 0.20/0.49    k2_struct_0(sK3) != k2_struct_0(sK3) | ~l1_struct_0(sK3) | spl5_2),
% 0.20/0.49    inference(superposition,[],[f168,f47])).
% 0.20/0.49  fof(f168,plain,(
% 0.20/0.49    u1_struct_0(sK3) != k2_struct_0(sK3) | spl5_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f166])).
% 0.20/0.49  fof(f352,plain,(
% 0.20/0.49    spl5_28 | ~spl5_2 | ~spl5_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f351,f171,f166,f336])).
% 0.20/0.49  fof(f171,plain,(
% 0.20/0.49    spl5_3 <=> v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.49  fof(f351,plain,(
% 0.20/0.49    u1_struct_0(sK3) != k2_struct_0(sK3) | v1_funct_1(k2_funct_1(sK4)) | ~spl5_3),
% 0.20/0.49    inference(forward_demodulation,[],[f350,f44])).
% 0.20/0.49  fof(f350,plain,(
% 0.20/0.49    v1_funct_1(k2_funct_1(sK4)) | u1_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | ~spl5_3),
% 0.20/0.49    inference(subsumption_resolution,[],[f349,f41])).
% 0.20/0.49  fof(f349,plain,(
% 0.20/0.49    v1_funct_1(k2_funct_1(sK4)) | u1_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | ~v1_funct_1(sK4) | ~spl5_3),
% 0.20/0.49    inference(subsumption_resolution,[],[f348,f42])).
% 0.20/0.49  fof(f348,plain,(
% 0.20/0.49    v1_funct_1(k2_funct_1(sK4)) | u1_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~spl5_3),
% 0.20/0.49    inference(subsumption_resolution,[],[f347,f43])).
% 0.20/0.49  fof(f347,plain,(
% 0.20/0.49    v1_funct_1(k2_funct_1(sK4)) | u1_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~spl5_3),
% 0.20/0.49    inference(subsumption_resolution,[],[f342,f45])).
% 0.20/0.49  fof(f342,plain,(
% 0.20/0.49    v1_funct_1(k2_funct_1(sK4)) | ~v2_funct_1(sK4) | u1_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~spl5_3),
% 0.20/0.49    inference(superposition,[],[f172,f60])).
% 0.20/0.49  fof(f172,plain,(
% 0.20/0.49    v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) | ~spl5_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f171])).
% 0.20/0.49  fof(f325,plain,(
% 0.20/0.49    spl5_3),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f324])).
% 0.20/0.49  fof(f324,plain,(
% 0.20/0.49    $false | spl5_3),
% 0.20/0.49    inference(subsumption_resolution,[],[f320,f111])).
% 0.20/0.49  fof(f111,plain,(
% 0.20/0.49    sP1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),
% 0.20/0.49    inference(subsumption_resolution,[],[f110,f41])).
% 0.20/0.49  fof(f110,plain,(
% 0.20/0.49    sP1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | ~v1_funct_1(sK4)),
% 0.20/0.49    inference(subsumption_resolution,[],[f105,f42])).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    sP1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 0.20/0.49    inference(resolution,[],[f59,f43])).
% 0.20/0.49  fof(f320,plain,(
% 0.20/0.49    ~sP1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | spl5_3),
% 0.20/0.49    inference(resolution,[],[f173,f56])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v1_funct_1(k2_tops_2(X0,X1,X2)) | ~sP1(X0,X1,X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f173,plain,(
% 0.20/0.49    ~v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) | spl5_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f171])).
% 0.20/0.49  fof(f225,plain,(
% 0.20/0.49    ~spl5_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f224,f162])).
% 0.20/0.49  fof(f224,plain,(
% 0.20/0.49    ~r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4)),
% 0.20/0.49    inference(subsumption_resolution,[],[f223,f41])).
% 0.20/0.49  fof(f223,plain,(
% 0.20/0.49    ~r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4) | ~v1_funct_1(sK4)),
% 0.20/0.49    inference(subsumption_resolution,[],[f222,f80])).
% 0.20/0.49  fof(f222,plain,(
% 0.20/0.49    ~r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4) | ~v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 0.20/0.49    inference(subsumption_resolution,[],[f221,f79])).
% 0.20/0.49  fof(f221,plain,(
% 0.20/0.49    ~r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 0.20/0.49    inference(subsumption_resolution,[],[f220,f78])).
% 0.20/0.49  fof(f220,plain,(
% 0.20/0.49    ~r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 0.20/0.49    inference(subsumption_resolution,[],[f146,f45])).
% 0.20/0.49  fof(f146,plain,(
% 0.20/0.49    ~r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4) | ~v2_funct_1(sK4) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 0.20/0.49    inference(superposition,[],[f77,f60])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    ~r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4)),sK4)),
% 0.20/0.49    inference(subsumption_resolution,[],[f69,f40])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    ~r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4)),sK4) | ~l1_struct_0(sK3)),
% 0.20/0.49    inference(superposition,[],[f46,f47])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK4)),
% 0.20/0.49    inference(cnf_transformation,[],[f34])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (10282)------------------------------
% 0.20/0.49  % (10282)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (10282)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (10282)Memory used [KB]: 6652
% 0.20/0.49  % (10282)Time elapsed: 0.039 s
% 0.20/0.49  % (10282)------------------------------
% 0.20/0.49  % (10282)------------------------------
% 0.20/0.49  % (10277)Success in time 0.134 s
%------------------------------------------------------------------------------
