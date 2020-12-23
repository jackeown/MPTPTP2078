%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  152 (2825 expanded)
%              Number of leaves         :   19 (1012 expanded)
%              Depth                    :   23
%              Number of atoms          :  551 (21215 expanded)
%              Number of equality atoms :  130 (3115 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f634,plain,(
    $false ),
    inference(subsumption_resolution,[],[f623,f57])).

fof(f57,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f623,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[],[f137,f618])).

fof(f618,plain,(
    k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f617,f220])).

fof(f220,plain,
    ( r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(superposition,[],[f192,f210])).

fof(f210,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f209,f96])).

fof(f96,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f95,f94])).

fof(f94,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f93,f87])).

fof(f87,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f58,f48])).

fof(f48,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f44,f43,f42])).

fof(f42,plain,
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
              ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2)
            & v2_funct_1(X2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2)
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
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

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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

fof(f58,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f93,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f53,f88])).

fof(f88,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f58,f50])).

fof(f50,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f45])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f59,f67])).

fof(f67,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f209,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f208,f101])).

fof(f101,plain,(
    v4_relat_1(sK2,k2_struct_0(sK0)) ),
    inference(resolution,[],[f71,f94])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f208,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f206,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f206,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f205,f128])).

fof(f128,plain,(
    k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(superposition,[],[f127,f99])).

fof(f99,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(forward_demodulation,[],[f98,f87])).

fof(f98,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(forward_demodulation,[],[f54,f88])).

fof(f54,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f127,plain,(
    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f70,f94])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

% (22866)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f205,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | v1_partfun1(sK2,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f203,f91])).

fof(f91,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f90,f87])).

fof(f90,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(superposition,[],[f52,f88])).

fof(f52,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f203,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | v1_partfun1(sK2,k2_struct_0(sK0)) ),
    inference(resolution,[],[f201,f94])).

fof(f201,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k1_xboole_0 = X0
      | ~ v1_funct_2(sK2,X1,X0)
      | v1_partfun1(sK2,X1) ) ),
    inference(resolution,[],[f85,f51])).

fof(f51,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

fof(f192,plain,(
    r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2) ),
    inference(forward_demodulation,[],[f191,f128])).

fof(f191,plain,(
    r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) ),
    inference(subsumption_resolution,[],[f189,f91])).

fof(f189,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) ),
    inference(resolution,[],[f187,f94])).

fof(f187,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1)
      | r2_funct_2(X0,X1,sK2,sK2) ) ),
    inference(resolution,[],[f84,f51])).

fof(f84,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | r2_funct_2(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f83])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f617,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f616])).

fof(f616,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | k1_xboole_0 = k2_relat_1(sK2)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(superposition,[],[f469,f615])).

fof(f615,plain,
    ( sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f614,f356])).

fof(f356,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(superposition,[],[f351,f210])).

fof(f351,plain,(
    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f350,f128])).

fof(f350,plain,(
    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f349,f91])).

fof(f349,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f346,f99])).

fof(f346,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(resolution,[],[f344,f94])).

fof(f344,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_2(k2_funct_1(sK2),X1,X0)
      | k2_relset_1(X0,X1,sK2) != X1
      | ~ v1_funct_2(sK2,X0,X1) ) ),
    inference(subsumption_resolution,[],[f342,f51])).

fof(f342,plain,(
    ! [X0,X1] :
      ( k2_relset_1(X0,X1,sK2) != X1
      | v1_funct_2(k2_funct_1(sK2),X1,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f74,f55])).

fof(f55,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_2(k2_funct_1(X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f614,plain,
    ( sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f611,f433])).

fof(f433,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(superposition,[],[f426,f210])).

fof(f426,plain,(
    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f407,f122])).

fof(f122,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f121,f96])).

fof(f121,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f119,f51])).

fof(f119,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f66,f55])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f407,plain,(
    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(resolution,[],[f397,f70])).

fof(f397,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f396,f128])).

fof(f396,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f395,f91])).

fof(f395,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f392,f99])).

fof(f392,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(resolution,[],[f390,f94])).

fof(f390,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,sK2) != X1
      | ~ v1_funct_2(sK2,X0,X1) ) ),
    inference(subsumption_resolution,[],[f388,f51])).

fof(f388,plain,(
    ! [X0,X1] :
      ( k2_relset_1(X0,X1,sK2) != X1
      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f75,f55])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f611,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(resolution,[],[f607,f411])).

fof(f411,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(superposition,[],[f397,f210])).

fof(f607,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,k2_funct_1(sK2)) != X1
      | sK2 = k2_tops_2(X0,X1,k2_funct_1(sK2))
      | ~ v1_funct_2(k2_funct_1(sK2),X0,X1) ) ),
    inference(forward_demodulation,[],[f606,f106])).

fof(f106,plain,(
    sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f105,f96])).

fof(f105,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f103,f51])).

fof(f103,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f64,f55])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(f606,plain,(
    ! [X0,X1] :
      ( k2_relset_1(X0,X1,k2_funct_1(sK2)) != X1
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(k2_funct_1(sK2),X0,X1)
      | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X0,X1,k2_funct_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f605,f96])).

fof(f605,plain,(
    ! [X0,X1] :
      ( k2_relset_1(X0,X1,k2_funct_1(sK2)) != X1
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(k2_funct_1(sK2),X0,X1)
      | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X0,X1,k2_funct_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f603,f51])).

fof(f603,plain,(
    ! [X0,X1] :
      ( k2_relset_1(X0,X1,k2_funct_1(sK2)) != X1
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(k2_funct_1(sK2),X0,X1)
      | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X0,X1,k2_funct_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f456,f55])).

fof(f456,plain,(
    ! [X4,X2,X3] :
      ( ~ v2_funct_1(X2)
      | k2_relset_1(X3,X4,k2_funct_1(X2)) != X4
      | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(k2_funct_1(X2),X3,X4)
      | k2_funct_1(k2_funct_1(X2)) = k2_tops_2(X3,X4,k2_funct_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f454,f62])).

fof(f62,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f454,plain,(
    ! [X4,X2,X3] :
      ( k2_funct_1(k2_funct_1(X2)) = k2_tops_2(X3,X4,k2_funct_1(X2))
      | k2_relset_1(X3,X4,k2_funct_1(X2)) != X4
      | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(k2_funct_1(X2),X3,X4)
      | ~ v1_funct_1(k2_funct_1(X2))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f76,f63])).

fof(f63,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f469,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(superposition,[],[f468,f210])).

fof(f468,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),sK2) ),
    inference(superposition,[],[f186,f462])).

fof(f462,plain,(
    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(forward_demodulation,[],[f461,f128])).

fof(f461,plain,(
    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f460,f91])).

fof(f460,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f457,f99])).

fof(f457,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(resolution,[],[f455,f94])).

fof(f455,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,sK2) != X1
      | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)
      | ~ v1_funct_2(sK2,X0,X1) ) ),
    inference(subsumption_resolution,[],[f453,f51])).

fof(f453,plain,(
    ! [X0,X1] :
      ( k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)
      | k2_relset_1(X0,X1,sK2) != X1
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f76,f55])).

fof(f186,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2) ),
    inference(forward_demodulation,[],[f185,f87])).

fof(f185,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2) ),
    inference(forward_demodulation,[],[f184,f128])).

fof(f184,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) ),
    inference(forward_demodulation,[],[f56,f88])).

fof(f56,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f137,plain,(
    ~ v1_xboole_0(k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f136,f49])).

fof(f49,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f136,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f135,f50])).

fof(f135,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(superposition,[],[f60,f128])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n011.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:35:12 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.49  % (22868)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.49  % (22868)Refutation not found, incomplete strategy% (22868)------------------------------
% 0.21/0.49  % (22868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (22868)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (22868)Memory used [KB]: 6140
% 0.21/0.49  % (22868)Time elapsed: 0.071 s
% 0.21/0.49  % (22868)------------------------------
% 0.21/0.49  % (22868)------------------------------
% 0.21/0.49  % (22884)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.50  % (22867)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (22886)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.51  % (22884)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f634,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f623,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.51  fof(f623,plain,(
% 0.21/0.51    ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    inference(superposition,[],[f137,f618])).
% 0.21/0.51  fof(f618,plain,(
% 0.21/0.51    k1_xboole_0 = k2_relat_1(sK2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f617,f220])).
% 0.21/0.51  fof(f220,plain,(
% 0.21/0.51    r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.21/0.51    inference(superposition,[],[f192,f210])).
% 0.21/0.51  fof(f210,plain,(
% 0.21/0.51    k2_struct_0(sK0) = k1_relat_1(sK2) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f209,f96])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    v1_relat_1(sK2)),
% 0.21/0.51    inference(resolution,[],[f95,f94])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.21/0.51    inference(forward_demodulation,[],[f93,f87])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.51    inference(resolution,[],[f58,f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    l1_struct_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f44,f43,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,negated_conjecture,(
% 0.21/0.51    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.21/0.51    inference(negated_conjecture,[],[f16])).
% 0.21/0.51  fof(f16,conjecture,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))),
% 0.21/0.51    inference(forward_demodulation,[],[f53,f88])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.21/0.51    inference(resolution,[],[f58,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    l1_struct_0(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f45])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.51    inference(cnf_transformation,[],[f45])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) )),
% 0.21/0.51    inference(resolution,[],[f59,f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.51  fof(f209,plain,(
% 0.21/0.51    k1_xboole_0 = k2_relat_1(sK2) | k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f208,f101])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    v4_relat_1(sK2,k2_struct_0(sK0))),
% 0.21/0.51    inference(resolution,[],[f71,f94])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.51  fof(f208,plain,(
% 0.21/0.51    k1_xboole_0 = k2_relat_1(sK2) | k2_struct_0(sK0) = k1_relat_1(sK2) | ~v4_relat_1(sK2,k2_struct_0(sK0)) | ~v1_relat_1(sK2)),
% 0.21/0.51    inference(resolution,[],[f206,f68])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | k1_relat_1(X1) = X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 0.21/0.51  fof(f206,plain,(
% 0.21/0.51    v1_partfun1(sK2,k2_struct_0(sK0)) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.21/0.51    inference(forward_demodulation,[],[f205,f128])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.21/0.51    inference(superposition,[],[f127,f99])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.21/0.51    inference(forward_demodulation,[],[f98,f87])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.21/0.51    inference(forward_demodulation,[],[f54,f88])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f45])).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)),
% 0.21/0.51    inference(resolution,[],[f70,f94])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  % (22866)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.51  fof(f205,plain,(
% 0.21/0.51    k1_xboole_0 = k2_struct_0(sK1) | v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.21/0.51    inference(subsumption_resolution,[],[f203,f91])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.21/0.51    inference(forward_demodulation,[],[f90,f87])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))),
% 0.21/0.51    inference(superposition,[],[f52,f88])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f45])).
% 0.21/0.51  fof(f203,plain,(
% 0.21/0.51    k1_xboole_0 = k2_struct_0(sK1) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.21/0.51    inference(resolution,[],[f201,f94])).
% 0.21/0.51  fof(f201,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_xboole_0 = X0 | ~v1_funct_2(sK2,X1,X0) | v1_partfun1(sK2,X1)) )),
% 0.21/0.51    inference(resolution,[],[f85,f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    v1_funct_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f45])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f77])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).
% 0.21/0.51  fof(f192,plain,(
% 0.21/0.51    r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2)),
% 0.21/0.51    inference(forward_demodulation,[],[f191,f128])).
% 0.21/0.51  fof(f191,plain,(
% 0.21/0.51    r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f189,f91])).
% 0.21/0.51  fof(f189,plain,(
% 0.21/0.51    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)),
% 0.21/0.51    inference(resolution,[],[f187,f94])).
% 0.21/0.51  fof(f187,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | r2_funct_2(X0,X1,sK2,sK2)) )),
% 0.21/0.51    inference(resolution,[],[f84,f51])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | r2_funct_2(X0,X1,X3,X3)) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f83])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.51    inference(equality_resolution,[],[f80])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.51    inference(nnf_transformation,[],[f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 0.21/0.51  fof(f617,plain,(
% 0.21/0.51    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f616])).
% 0.21/0.51  fof(f616,plain,(
% 0.21/0.51    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | k1_xboole_0 = k2_relat_1(sK2) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.21/0.51    inference(superposition,[],[f469,f615])).
% 0.21/0.51  fof(f615,plain,(
% 0.21/0.51    sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f614,f356])).
% 0.21/0.51  fof(f356,plain,(
% 0.21/0.51    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.21/0.51    inference(superposition,[],[f351,f210])).
% 0.21/0.51  fof(f351,plain,(
% 0.21/0.51    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))),
% 0.21/0.51    inference(forward_demodulation,[],[f350,f128])).
% 0.21/0.51  fof(f350,plain,(
% 0.21/0.51    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))),
% 0.21/0.51    inference(subsumption_resolution,[],[f349,f91])).
% 0.21/0.51  fof(f349,plain,(
% 0.21/0.51    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f346,f99])).
% 0.21/0.51  fof(f346,plain,(
% 0.21/0.51    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.21/0.51    inference(resolution,[],[f344,f94])).
% 0.21/0.51  fof(f344,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(k2_funct_1(sK2),X1,X0) | k2_relset_1(X0,X1,sK2) != X1 | ~v1_funct_2(sK2,X0,X1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f342,f51])).
% 0.21/0.51  fof(f342,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_relset_1(X0,X1,sK2) != X1 | v1_funct_2(k2_funct_1(sK2),X1,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) )),
% 0.21/0.51    inference(resolution,[],[f74,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    v2_funct_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f45])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_2(k2_funct_1(X2),X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.21/0.51  fof(f614,plain,(
% 0.21/0.51    sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f611,f433])).
% 0.21/0.51  fof(f433,plain,(
% 0.21/0.51    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.21/0.51    inference(superposition,[],[f426,f210])).
% 0.21/0.51  fof(f426,plain,(
% 0.21/0.51    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.21/0.51    inference(forward_demodulation,[],[f407,f122])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.21/0.51    inference(subsumption_resolution,[],[f121,f96])).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f119,f51])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.21/0.51    inference(resolution,[],[f66,f55])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.51  fof(f407,plain,(
% 0.21/0.51    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.21/0.51    inference(resolution,[],[f397,f70])).
% 0.21/0.51  fof(f397,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))),
% 0.21/0.51    inference(forward_demodulation,[],[f396,f128])).
% 0.21/0.51  fof(f396,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 0.21/0.51    inference(subsumption_resolution,[],[f395,f91])).
% 0.21/0.51  fof(f395,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f392,f99])).
% 0.21/0.51  fof(f392,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.21/0.51    inference(resolution,[],[f390,f94])).
% 0.21/0.51  fof(f390,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,sK2) != X1 | ~v1_funct_2(sK2,X0,X1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f388,f51])).
% 0.21/0.51  fof(f388,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_relset_1(X0,X1,sK2) != X1 | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) )),
% 0.21/0.51    inference(resolution,[],[f75,f55])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f35])).
% 0.21/0.51  fof(f611,plain,(
% 0.21/0.51    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.21/0.51    inference(resolution,[],[f607,f411])).
% 0.21/0.51  fof(f411,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.21/0.51    inference(superposition,[],[f397,f210])).
% 0.21/0.51  fof(f607,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,k2_funct_1(sK2)) != X1 | sK2 = k2_tops_2(X0,X1,k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),X0,X1)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f606,f106])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    sK2 = k2_funct_1(k2_funct_1(sK2))),
% 0.21/0.51    inference(subsumption_resolution,[],[f105,f96])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f103,f51])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.21/0.51    inference(resolution,[],[f64,f55])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_funct_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
% 0.21/0.51  fof(f606,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_relset_1(X0,X1,k2_funct_1(sK2)) != X1 | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(k2_funct_1(sK2),X0,X1) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X0,X1,k2_funct_1(sK2))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f605,f96])).
% 0.21/0.51  fof(f605,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_relset_1(X0,X1,k2_funct_1(sK2)) != X1 | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(k2_funct_1(sK2),X0,X1) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X0,X1,k2_funct_1(sK2)) | ~v1_relat_1(sK2)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f603,f51])).
% 0.21/0.51  fof(f603,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_relset_1(X0,X1,k2_funct_1(sK2)) != X1 | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(k2_funct_1(sK2),X0,X1) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X0,X1,k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.21/0.51    inference(resolution,[],[f456,f55])).
% 0.21/0.51  fof(f456,plain,(
% 0.21/0.51    ( ! [X4,X2,X3] : (~v2_funct_1(X2) | k2_relset_1(X3,X4,k2_funct_1(X2)) != X4 | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(k2_funct_1(X2),X3,X4) | k2_funct_1(k2_funct_1(X2)) = k2_tops_2(X3,X4,k2_funct_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f454,f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).
% 0.21/0.51  fof(f454,plain,(
% 0.21/0.51    ( ! [X4,X2,X3] : (k2_funct_1(k2_funct_1(X2)) = k2_tops_2(X3,X4,k2_funct_1(X2)) | k2_relset_1(X3,X4,k2_funct_1(X2)) != X4 | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(k2_funct_1(X2),X3,X4) | ~v1_funct_1(k2_funct_1(X2)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.51    inference(resolution,[],[f76,f63])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 0.21/0.51  fof(f469,plain,(
% 0.21/0.51    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.21/0.51    inference(superposition,[],[f468,f210])).
% 0.21/0.51  fof(f468,plain,(
% 0.21/0.51    ~r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),sK2)),
% 0.21/0.51    inference(superposition,[],[f186,f462])).
% 0.21/0.51  fof(f462,plain,(
% 0.21/0.51    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.21/0.51    inference(forward_demodulation,[],[f461,f128])).
% 0.21/0.51  fof(f461,plain,(
% 0.21/0.51    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f460,f91])).
% 0.21/0.51  fof(f460,plain,(
% 0.21/0.51    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f457,f99])).
% 0.21/0.51  fof(f457,plain,(
% 0.21/0.51    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.21/0.51    inference(resolution,[],[f455,f94])).
% 0.21/0.51  fof(f455,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1 | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) | ~v1_funct_2(sK2,X0,X1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f453,f51])).
% 0.21/0.51  fof(f453,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) | k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) )),
% 0.21/0.51    inference(resolution,[],[f76,f55])).
% 0.21/0.51  fof(f186,plain,(
% 0.21/0.51    ~r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2)),
% 0.21/0.51    inference(forward_demodulation,[],[f185,f87])).
% 0.21/0.51  fof(f185,plain,(
% 0.21/0.51    ~r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2)),
% 0.21/0.51    inference(forward_demodulation,[],[f184,f128])).
% 0.21/0.51  fof(f184,plain,(
% 0.21/0.51    ~r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)),
% 0.21/0.51    inference(forward_demodulation,[],[f56,f88])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f45])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    ~v1_xboole_0(k2_relat_1(sK2))),
% 0.21/0.51    inference(subsumption_resolution,[],[f136,f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ~v2_struct_0(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f45])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    ~v1_xboole_0(k2_relat_1(sK2)) | v2_struct_0(sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f135,f50])).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    ~v1_xboole_0(k2_relat_1(sK2)) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 0.21/0.51    inference(superposition,[],[f60,f128])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,axiom,(
% 0.21/0.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (22884)------------------------------
% 0.21/0.51  % (22884)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (22884)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (22884)Memory used [KB]: 6524
% 0.21/0.51  % (22884)Time elapsed: 0.099 s
% 0.21/0.51  % (22884)------------------------------
% 0.21/0.51  % (22884)------------------------------
% 0.21/0.51  % (22859)Success in time 0.15 s
%------------------------------------------------------------------------------
