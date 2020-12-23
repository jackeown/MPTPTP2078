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
% DateTime   : Thu Dec  3 13:14:34 EST 2020

% Result     : Theorem 0.11s
% Output     : Refutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 920 expanded)
%              Number of leaves         :   13 ( 341 expanded)
%              Depth                    :   22
%              Number of atoms          :  507 (7717 expanded)
%              Number of equality atoms :  110 (1089 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f229,plain,(
    $false ),
    inference(subsumption_resolution,[],[f228,f68])).

fof(f68,plain,(
    r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) ),
    inference(forward_demodulation,[],[f67,f57])).

fof(f57,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f43,f33])).

fof(f33,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f30,f29,f28])).

fof(f28,plain,
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

fof(f29,plain,
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

fof(f30,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).

fof(f43,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f67,plain,(
    r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) ),
    inference(forward_demodulation,[],[f66,f58])).

fof(f58,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f43,f35])).

fof(f35,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f66,plain,(
    r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK2) ),
    inference(subsumption_resolution,[],[f65,f36])).

fof(f36,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f65,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f64,f37])).

fof(f37,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f64,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f56,f38])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f31])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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

fof(f228,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) ),
    inference(superposition,[],[f144,f201])).

fof(f201,plain,(
    sK2 = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f200,f63])).

fof(f63,plain,(
    sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f62,f60])).

fof(f60,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f59,f48])).

fof(f48,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f59,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(resolution,[],[f42,f38])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f62,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f61,f36])).

fof(f61,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f47,f40])).

fof(f40,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(f200,plain,(
    k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f199,f74])).

fof(f74,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f73,f58])).

fof(f73,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f72,f39])).

fof(f39,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f72,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f71,f36])).

fof(f71,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f70,f37])).

fof(f70,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f69,f40])).

fof(f69,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f49,f38])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | v1_funct_1(k2_funct_1(X2))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f199,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f198,f82])).

fof(f82,plain,(
    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f81,f58])).

fof(f81,plain,(
    v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f80,f57])).

fof(f80,plain,(
    v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f79,f58])).

fof(f79,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f78,f39])).

fof(f78,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f77,f36])).

fof(f77,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f76,f37])).

fof(f76,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f75,f40])).

fof(f75,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f50,f38])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | v1_funct_2(k2_funct_1(X2),X1,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f198,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f197,f130])).

fof(f130,plain,(
    k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f129,f98])).

fof(f98,plain,(
    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(forward_demodulation,[],[f97,f57])).

fof(f97,plain,(
    k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(forward_demodulation,[],[f96,f58])).

fof(f96,plain,(
    k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f95,f58])).

fof(f95,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(forward_demodulation,[],[f94,f39])).

fof(f94,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f93,f36])).

fof(f93,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f92,f37])).

fof(f92,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f91,f40])).

fof(f91,plain,
    ( ~ v2_funct_1(sK2)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f52,f38])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f129,plain,(
    k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(forward_demodulation,[],[f128,f57])).

fof(f128,plain,(
    k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(forward_demodulation,[],[f127,f58])).

fof(f127,plain,(
    k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f126,f33])).

fof(f126,plain,
    ( k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f125,f34])).

fof(f34,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f125,plain,
    ( k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f124,f35])).

fof(f124,plain,
    ( k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f123,f36])).

fof(f123,plain,
    ( k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_1(sK2)
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f122,f37])).

fof(f122,plain,
    ( k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f121,f39])).

fof(f121,plain,
    ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f120,f40])).

fof(f120,plain,
    ( ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f46,f38])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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

fof(f197,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f191,f108])).

fof(f108,plain,(
    v2_funct_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f107,f98])).

fof(f107,plain,(
    v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(forward_demodulation,[],[f106,f57])).

fof(f106,plain,(
    v2_funct_1(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(forward_demodulation,[],[f105,f58])).

fof(f105,plain,(
    v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f104,f33])).

fof(f104,plain,
    ( v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f103,f35])).

fof(f103,plain,
    ( v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f102,f36])).

fof(f102,plain,
    ( v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_1(sK2)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f101,f37])).

fof(f101,plain,
    ( v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f100,f39])).

fof(f100,plain,
    ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f99,f40])).

fof(f99,plain,
    ( ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f44,f38])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f191,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f90,f52])).

fof(f90,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f89,f58])).

fof(f89,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f88,f57])).

fof(f88,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f87,f58])).

fof(f87,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f86,f39])).

fof(f86,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f85,f36])).

fof(f85,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f84,f37])).

fof(f84,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f83,f40])).

fof(f83,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f51,f38])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f144,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK2) ),
    inference(forward_demodulation,[],[f143,f98])).

fof(f143,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) ),
    inference(forward_demodulation,[],[f133,f58])).

fof(f133,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(superposition,[],[f41,f57])).

fof(f41,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.08  % Command    : run_vampire %s %d
% 0.07/0.26  % Computer   : n016.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.26  % CPULimit   : 60
% 0.07/0.26  % WCLimit    : 600
% 0.07/0.26  % DateTime   : Tue Dec  1 09:21:19 EST 2020
% 0.07/0.26  % CPUTime    : 
% 0.11/0.38  % (14853)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.11/0.39  % (14853)Refutation found. Thanks to Tanya!
% 0.11/0.39  % SZS status Theorem for theBenchmark
% 0.11/0.39  % (14861)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.11/0.39  % SZS output start Proof for theBenchmark
% 0.11/0.39  fof(f229,plain,(
% 0.11/0.39    $false),
% 0.11/0.39    inference(subsumption_resolution,[],[f228,f68])).
% 0.11/0.39  fof(f68,plain,(
% 0.11/0.39    r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)),
% 0.11/0.39    inference(forward_demodulation,[],[f67,f57])).
% 0.11/0.39  fof(f57,plain,(
% 0.11/0.39    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.11/0.39    inference(resolution,[],[f43,f33])).
% 0.11/0.39  fof(f33,plain,(
% 0.11/0.39    l1_struct_0(sK0)),
% 0.11/0.39    inference(cnf_transformation,[],[f31])).
% 0.11/0.39  fof(f31,plain,(
% 0.11/0.39    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.11/0.39    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f30,f29,f28])).
% 0.11/0.39  fof(f28,plain,(
% 0.11/0.39    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 0.11/0.39    introduced(choice_axiom,[])).
% 0.11/0.39  fof(f29,plain,(
% 0.11/0.39    ? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))),
% 0.11/0.39    introduced(choice_axiom,[])).
% 0.11/0.39  fof(f30,plain,(
% 0.11/0.39    ? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.11/0.39    introduced(choice_axiom,[])).
% 0.11/0.39  fof(f13,plain,(
% 0.11/0.39    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.11/0.39    inference(flattening,[],[f12])).
% 0.11/0.39  fof(f12,plain,(
% 0.11/0.39    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.11/0.39    inference(ennf_transformation,[],[f11])).
% 0.11/0.39  fof(f11,negated_conjecture,(
% 0.11/0.39    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.11/0.39    inference(negated_conjecture,[],[f10])).
% 0.11/0.39  fof(f10,conjecture,(
% 0.11/0.39    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.11/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).
% 0.11/0.39  fof(f43,plain,(
% 0.11/0.39    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.11/0.39    inference(cnf_transformation,[],[f15])).
% 0.11/0.39  fof(f15,plain,(
% 0.11/0.39    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.11/0.39    inference(ennf_transformation,[],[f6])).
% 0.11/0.39  fof(f6,axiom,(
% 0.11/0.39    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.11/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.11/0.39  fof(f67,plain,(
% 0.11/0.39    r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)),
% 0.11/0.39    inference(forward_demodulation,[],[f66,f58])).
% 0.11/0.39  fof(f58,plain,(
% 0.11/0.39    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.11/0.39    inference(resolution,[],[f43,f35])).
% 0.11/0.39  fof(f35,plain,(
% 0.11/0.39    l1_struct_0(sK1)),
% 0.11/0.39    inference(cnf_transformation,[],[f31])).
% 0.11/0.39  fof(f66,plain,(
% 0.11/0.39    r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK2)),
% 0.11/0.39    inference(subsumption_resolution,[],[f65,f36])).
% 0.11/0.39  fof(f36,plain,(
% 0.11/0.39    v1_funct_1(sK2)),
% 0.11/0.39    inference(cnf_transformation,[],[f31])).
% 0.11/0.39  fof(f65,plain,(
% 0.11/0.39    r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK2) | ~v1_funct_1(sK2)),
% 0.11/0.39    inference(subsumption_resolution,[],[f64,f37])).
% 0.11/0.39  fof(f37,plain,(
% 0.11/0.39    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.11/0.39    inference(cnf_transformation,[],[f31])).
% 0.11/0.39  fof(f64,plain,(
% 0.11/0.39    r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.11/0.39    inference(resolution,[],[f56,f38])).
% 0.11/0.39  fof(f38,plain,(
% 0.11/0.39    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.11/0.39    inference(cnf_transformation,[],[f31])).
% 0.11/0.39  fof(f56,plain,(
% 0.11/0.39    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X3,X3) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.11/0.39    inference(duplicate_literal_removal,[],[f55])).
% 0.11/0.39  fof(f55,plain,(
% 0.11/0.39    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.11/0.39    inference(equality_resolution,[],[f54])).
% 0.11/0.39  fof(f54,plain,(
% 0.11/0.39    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.11/0.39    inference(cnf_transformation,[],[f32])).
% 0.11/0.39  fof(f32,plain,(
% 0.11/0.39    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.11/0.39    inference(nnf_transformation,[],[f27])).
% 0.11/0.39  fof(f27,plain,(
% 0.11/0.39    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.11/0.39    inference(flattening,[],[f26])).
% 0.11/0.39  fof(f26,plain,(
% 0.11/0.39    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.11/0.39    inference(ennf_transformation,[],[f4])).
% 0.11/0.39  fof(f4,axiom,(
% 0.11/0.39    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 0.11/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 0.11/0.39  fof(f228,plain,(
% 0.11/0.39    ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)),
% 0.11/0.39    inference(superposition,[],[f144,f201])).
% 0.11/0.39  fof(f201,plain,(
% 0.11/0.39    sK2 = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.11/0.39    inference(forward_demodulation,[],[f200,f63])).
% 0.11/0.39  fof(f63,plain,(
% 0.11/0.39    sK2 = k2_funct_1(k2_funct_1(sK2))),
% 0.11/0.39    inference(subsumption_resolution,[],[f62,f60])).
% 0.11/0.39  fof(f60,plain,(
% 0.11/0.39    v1_relat_1(sK2)),
% 0.11/0.39    inference(subsumption_resolution,[],[f59,f48])).
% 0.11/0.39  fof(f48,plain,(
% 0.11/0.39    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.11/0.39    inference(cnf_transformation,[],[f2])).
% 0.11/0.39  fof(f2,axiom,(
% 0.11/0.39    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.11/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.11/0.39  fof(f59,plain,(
% 0.11/0.39    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))),
% 0.11/0.39    inference(resolution,[],[f42,f38])).
% 0.11/0.39  fof(f42,plain,(
% 0.11/0.39    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.11/0.39    inference(cnf_transformation,[],[f14])).
% 0.11/0.39  fof(f14,plain,(
% 0.11/0.39    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.11/0.39    inference(ennf_transformation,[],[f1])).
% 0.11/0.39  fof(f1,axiom,(
% 0.11/0.39    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.11/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.11/0.39  fof(f62,plain,(
% 0.11/0.39    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.11/0.39    inference(subsumption_resolution,[],[f61,f36])).
% 0.11/0.39  fof(f61,plain,(
% 0.11/0.39    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.11/0.39    inference(resolution,[],[f47,f40])).
% 0.11/0.39  fof(f40,plain,(
% 0.11/0.39    v2_funct_1(sK2)),
% 0.11/0.39    inference(cnf_transformation,[],[f31])).
% 0.11/0.39  fof(f47,plain,(
% 0.11/0.39    ( ! [X0] : (~v2_funct_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.11/0.39    inference(cnf_transformation,[],[f21])).
% 0.11/0.39  fof(f21,plain,(
% 0.11/0.39    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.11/0.39    inference(flattening,[],[f20])).
% 0.11/0.39  fof(f20,plain,(
% 0.11/0.39    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.11/0.39    inference(ennf_transformation,[],[f3])).
% 0.11/0.39  fof(f3,axiom,(
% 0.11/0.39    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.11/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
% 0.11/0.39  fof(f200,plain,(
% 0.11/0.39    k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.11/0.39    inference(subsumption_resolution,[],[f199,f74])).
% 0.11/0.39  fof(f74,plain,(
% 0.11/0.39    v1_funct_1(k2_funct_1(sK2))),
% 0.11/0.39    inference(subsumption_resolution,[],[f73,f58])).
% 0.11/0.39  fof(f73,plain,(
% 0.11/0.39    u1_struct_0(sK1) != k2_struct_0(sK1) | v1_funct_1(k2_funct_1(sK2))),
% 0.11/0.39    inference(forward_demodulation,[],[f72,f39])).
% 0.11/0.39  fof(f39,plain,(
% 0.11/0.39    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.11/0.39    inference(cnf_transformation,[],[f31])).
% 0.11/0.39  fof(f72,plain,(
% 0.11/0.39    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | v1_funct_1(k2_funct_1(sK2))),
% 0.11/0.39    inference(subsumption_resolution,[],[f71,f36])).
% 0.11/0.39  fof(f71,plain,(
% 0.11/0.39    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2)),
% 0.11/0.39    inference(subsumption_resolution,[],[f70,f37])).
% 0.11/0.39  fof(f70,plain,(
% 0.11/0.39    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.11/0.39    inference(subsumption_resolution,[],[f69,f40])).
% 0.11/0.40  fof(f69,plain,(
% 0.11/0.40    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.11/0.40    inference(resolution,[],[f49,f38])).
% 0.11/0.40  fof(f49,plain,(
% 0.11/0.40    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | v1_funct_1(k2_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.11/0.40    inference(cnf_transformation,[],[f23])).
% 0.11/0.40  fof(f23,plain,(
% 0.11/0.40    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.11/0.40    inference(flattening,[],[f22])).
% 0.11/0.40  fof(f22,plain,(
% 0.11/0.40    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.11/0.40    inference(ennf_transformation,[],[f5])).
% 0.11/0.40  fof(f5,axiom,(
% 0.11/0.40    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.11/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.11/0.40  fof(f199,plain,(
% 0.11/0.40    k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.11/0.40    inference(subsumption_resolution,[],[f198,f82])).
% 0.11/0.40  fof(f82,plain,(
% 0.11/0.40    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))),
% 0.11/0.40    inference(forward_demodulation,[],[f81,f58])).
% 0.11/0.40  fof(f81,plain,(
% 0.11/0.40    v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k2_struct_0(sK0))),
% 0.11/0.40    inference(forward_demodulation,[],[f80,f57])).
% 0.11/0.40  fof(f80,plain,(
% 0.11/0.40    v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.11/0.40    inference(subsumption_resolution,[],[f79,f58])).
% 0.11/0.40  fof(f79,plain,(
% 0.11/0.40    u1_struct_0(sK1) != k2_struct_0(sK1) | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.11/0.40    inference(forward_demodulation,[],[f78,f39])).
% 0.11/0.40  fof(f78,plain,(
% 0.11/0.40    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.11/0.40    inference(subsumption_resolution,[],[f77,f36])).
% 0.11/0.40  fof(f77,plain,(
% 0.11/0.40    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2)),
% 0.11/0.40    inference(subsumption_resolution,[],[f76,f37])).
% 0.11/0.40  fof(f76,plain,(
% 0.11/0.40    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.11/0.40    inference(subsumption_resolution,[],[f75,f40])).
% 0.11/0.40  fof(f75,plain,(
% 0.11/0.40    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.11/0.40    inference(resolution,[],[f50,f38])).
% 0.11/0.40  fof(f50,plain,(
% 0.11/0.40    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.11/0.40    inference(cnf_transformation,[],[f23])).
% 0.11/0.40  fof(f198,plain,(
% 0.11/0.40    k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.11/0.40    inference(subsumption_resolution,[],[f197,f130])).
% 0.11/0.40  fof(f130,plain,(
% 0.11/0.40    k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.11/0.40    inference(forward_demodulation,[],[f129,f98])).
% 0.11/0.40  fof(f98,plain,(
% 0.11/0.40    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.11/0.40    inference(forward_demodulation,[],[f97,f57])).
% 0.11/0.40  fof(f97,plain,(
% 0.11/0.40    k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.11/0.40    inference(forward_demodulation,[],[f96,f58])).
% 0.11/0.40  fof(f96,plain,(
% 0.11/0.40    k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)),
% 0.11/0.40    inference(subsumption_resolution,[],[f95,f58])).
% 0.11/0.40  fof(f95,plain,(
% 0.11/0.40    u1_struct_0(sK1) != k2_struct_0(sK1) | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)),
% 0.11/0.40    inference(forward_demodulation,[],[f94,f39])).
% 0.11/0.40  fof(f94,plain,(
% 0.11/0.40    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)),
% 0.11/0.40    inference(subsumption_resolution,[],[f93,f36])).
% 0.11/0.40  fof(f93,plain,(
% 0.11/0.40    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) | ~v1_funct_1(sK2)),
% 0.11/0.40    inference(subsumption_resolution,[],[f92,f37])).
% 0.11/0.40  fof(f92,plain,(
% 0.11/0.40    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.11/0.40    inference(subsumption_resolution,[],[f91,f40])).
% 0.11/0.40  fof(f91,plain,(
% 0.11/0.40    ~v2_funct_1(sK2) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.11/0.40    inference(resolution,[],[f52,f38])).
% 0.11/0.40  fof(f52,plain,(
% 0.11/0.40    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.11/0.40    inference(cnf_transformation,[],[f25])).
% 0.11/0.40  fof(f25,plain,(
% 0.11/0.40    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.11/0.40    inference(flattening,[],[f24])).
% 0.11/0.40  fof(f24,plain,(
% 0.11/0.40    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.11/0.40    inference(ennf_transformation,[],[f7])).
% 0.11/0.40  fof(f7,axiom,(
% 0.11/0.40    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.11/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 0.11/0.40  fof(f129,plain,(
% 0.11/0.40    k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.11/0.40    inference(forward_demodulation,[],[f128,f57])).
% 0.11/0.40  fof(f128,plain,(
% 0.11/0.40    k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.11/0.40    inference(forward_demodulation,[],[f127,f58])).
% 0.11/0.40  fof(f127,plain,(
% 0.11/0.40    k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.11/0.40    inference(subsumption_resolution,[],[f126,f33])).
% 0.11/0.40  fof(f126,plain,(
% 0.11/0.40    k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~l1_struct_0(sK0)),
% 0.11/0.40    inference(subsumption_resolution,[],[f125,f34])).
% 0.11/0.40  fof(f34,plain,(
% 0.11/0.40    ~v2_struct_0(sK1)),
% 0.11/0.40    inference(cnf_transformation,[],[f31])).
% 0.11/0.40  fof(f125,plain,(
% 0.11/0.40    k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | v2_struct_0(sK1) | ~l1_struct_0(sK0)),
% 0.11/0.40    inference(subsumption_resolution,[],[f124,f35])).
% 0.11/0.40  fof(f124,plain,(
% 0.11/0.40    k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~l1_struct_0(sK0)),
% 0.11/0.40    inference(subsumption_resolution,[],[f123,f36])).
% 0.11/0.40  fof(f123,plain,(
% 0.11/0.40    k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_1(sK2) | ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~l1_struct_0(sK0)),
% 0.11/0.40    inference(subsumption_resolution,[],[f122,f37])).
% 0.11/0.40  fof(f122,plain,(
% 0.11/0.40    k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~l1_struct_0(sK0)),
% 0.11/0.40    inference(subsumption_resolution,[],[f121,f39])).
% 0.11/0.40  fof(f121,plain,(
% 0.11/0.40    k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~l1_struct_0(sK0)),
% 0.11/0.40    inference(subsumption_resolution,[],[f120,f40])).
% 0.11/0.40  fof(f120,plain,(
% 0.11/0.40    ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~l1_struct_0(sK0)),
% 0.11/0.40    inference(resolution,[],[f46,f38])).
% 0.11/0.40  fof(f46,plain,(
% 0.11/0.40    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.11/0.40    inference(cnf_transformation,[],[f19])).
% 0.11/0.40  fof(f19,plain,(
% 0.11/0.40    ! [X0] : (! [X1] : (! [X2] : ((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.11/0.40    inference(flattening,[],[f18])).
% 0.11/0.40  fof(f18,plain,(
% 0.11/0.40    ! [X0] : (! [X1] : (! [X2] : (((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_struct_0(X1) | v2_struct_0(X1))) | ~l1_struct_0(X0))),
% 0.11/0.40    inference(ennf_transformation,[],[f8])).
% 0.11/0.40  fof(f8,axiom,(
% 0.11/0.40    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.11/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).
% 0.11/0.40  fof(f197,plain,(
% 0.11/0.40    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.11/0.40    inference(subsumption_resolution,[],[f191,f108])).
% 0.11/0.40  fof(f108,plain,(
% 0.11/0.40    v2_funct_1(k2_funct_1(sK2))),
% 0.11/0.40    inference(forward_demodulation,[],[f107,f98])).
% 0.11/0.40  fof(f107,plain,(
% 0.11/0.40    v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.11/0.40    inference(forward_demodulation,[],[f106,f57])).
% 0.11/0.40  fof(f106,plain,(
% 0.11/0.40    v2_funct_1(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.11/0.40    inference(forward_demodulation,[],[f105,f58])).
% 0.11/0.40  fof(f105,plain,(
% 0.11/0.40    v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.11/0.40    inference(subsumption_resolution,[],[f104,f33])).
% 0.11/0.40  fof(f104,plain,(
% 0.11/0.40    v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~l1_struct_0(sK0)),
% 0.11/0.40    inference(subsumption_resolution,[],[f103,f35])).
% 0.11/0.40  fof(f103,plain,(
% 0.11/0.40    v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~l1_struct_0(sK1) | ~l1_struct_0(sK0)),
% 0.11/0.40    inference(subsumption_resolution,[],[f102,f36])).
% 0.11/0.40  fof(f102,plain,(
% 0.11/0.40    v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_1(sK2) | ~l1_struct_0(sK1) | ~l1_struct_0(sK0)),
% 0.11/0.40    inference(subsumption_resolution,[],[f101,f37])).
% 0.11/0.40  fof(f101,plain,(
% 0.11/0.40    v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_struct_0(sK1) | ~l1_struct_0(sK0)),
% 0.11/0.40    inference(subsumption_resolution,[],[f100,f39])).
% 0.11/0.40  fof(f100,plain,(
% 0.11/0.40    k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_struct_0(sK1) | ~l1_struct_0(sK0)),
% 0.11/0.40    inference(subsumption_resolution,[],[f99,f40])).
% 0.11/0.40  fof(f99,plain,(
% 0.11/0.40    ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_struct_0(sK1) | ~l1_struct_0(sK0)),
% 0.11/0.40    inference(resolution,[],[f44,f38])).
% 0.11/0.40  fof(f44,plain,(
% 0.11/0.40    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.11/0.40    inference(cnf_transformation,[],[f17])).
% 0.11/0.40  fof(f17,plain,(
% 0.11/0.40    ! [X0] : (! [X1] : (! [X2] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.11/0.40    inference(flattening,[],[f16])).
% 0.11/0.40  fof(f16,plain,(
% 0.11/0.40    ! [X0] : (! [X1] : (! [X2] : ((v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.11/0.40    inference(ennf_transformation,[],[f9])).
% 0.11/0.40  fof(f9,axiom,(
% 0.11/0.40    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 0.11/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_tops_2)).
% 0.11/0.40  fof(f191,plain,(
% 0.11/0.40    ~v2_funct_1(k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.11/0.40    inference(resolution,[],[f90,f52])).
% 0.11/0.40  fof(f90,plain,(
% 0.11/0.40    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 0.11/0.40    inference(forward_demodulation,[],[f89,f58])).
% 0.11/0.40  fof(f89,plain,(
% 0.11/0.40    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK0))))),
% 0.11/0.40    inference(forward_demodulation,[],[f88,f57])).
% 0.11/0.40  fof(f88,plain,(
% 0.11/0.40    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.11/0.40    inference(subsumption_resolution,[],[f87,f58])).
% 0.11/0.40  fof(f87,plain,(
% 0.11/0.40    u1_struct_0(sK1) != k2_struct_0(sK1) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.11/0.40    inference(forward_demodulation,[],[f86,f39])).
% 0.11/0.40  fof(f86,plain,(
% 0.11/0.40    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.11/0.40    inference(subsumption_resolution,[],[f85,f36])).
% 0.11/0.40  fof(f85,plain,(
% 0.11/0.40    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(sK2)),
% 0.11/0.40    inference(subsumption_resolution,[],[f84,f37])).
% 0.11/0.40  fof(f84,plain,(
% 0.11/0.40    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.11/0.40    inference(subsumption_resolution,[],[f83,f40])).
% 0.11/0.40  fof(f83,plain,(
% 0.11/0.40    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.11/0.40    inference(resolution,[],[f51,f38])).
% 0.11/0.40  fof(f51,plain,(
% 0.11/0.40    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.11/0.40    inference(cnf_transformation,[],[f23])).
% 0.11/0.40  fof(f144,plain,(
% 0.11/0.40    ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK2)),
% 0.11/0.40    inference(forward_demodulation,[],[f143,f98])).
% 0.11/0.40  fof(f143,plain,(
% 0.11/0.40    ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)),
% 0.11/0.40    inference(forward_demodulation,[],[f133,f58])).
% 0.11/0.40  fof(f133,plain,(
% 0.11/0.40    ~r2_funct_2(k2_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 0.11/0.40    inference(superposition,[],[f41,f57])).
% 0.11/0.40  fof(f41,plain,(
% 0.11/0.40    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 0.11/0.40    inference(cnf_transformation,[],[f31])).
% 0.11/0.40  % SZS output end Proof for theBenchmark
% 0.11/0.40  % (14853)------------------------------
% 0.11/0.40  % (14853)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.40  % (14853)Termination reason: Refutation
% 0.11/0.40  
% 0.11/0.40  % (14853)Memory used [KB]: 10746
% 0.11/0.40  % (14853)Time elapsed: 0.061 s
% 0.11/0.40  % (14853)------------------------------
% 0.11/0.40  % (14853)------------------------------
% 0.11/0.40  % (14839)Success in time 0.125 s
%------------------------------------------------------------------------------
