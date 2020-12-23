%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 275 expanded)
%              Number of leaves         :   13 ( 113 expanded)
%              Depth                    :   21
%              Number of atoms          :  433 (2883 expanded)
%              Number of equality atoms :   36 (  36 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f99,plain,(
    $false ),
    inference(subsumption_resolution,[],[f98,f70])).

fof(f70,plain,(
    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3) ),
    inference(subsumption_resolution,[],[f69,f43])).

fof(f43,plain,(
    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(sK0,sK1,sK2,sK2,sK3))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    & v1_funct_1(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f29,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(sK0,X1,X2,X2,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(sK0,X1,X2,X2,X3))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                & v1_funct_1(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),X3,k3_tmap_1(sK0,sK1,X2,X2,X3))
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
              & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK1))
              & v1_funct_1(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),X3,k3_tmap_1(sK0,sK1,X2,X2,X3))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
            & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK1))
            & v1_funct_1(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X3,k3_tmap_1(sK0,sK1,sK2,sK2,X3))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
          & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK1))
          & v1_funct_1(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X3] :
        ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X3,k3_tmap_1(sK0,sK1,sK2,sK2,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK1))
        & v1_funct_1(X3) )
   => ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(sK0,sK1,sK2,sK2,sK3))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X3) )
                   => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tmap_1)).

fof(f69,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3) ),
    inference(resolution,[],[f67,f44])).

fof(f44,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f30])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK3,X0,X1)
      | r2_funct_2(X0,X1,sK3,sK3) ) ),
    inference(resolution,[],[f60,f42])).

fof(f42,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_funct_2(X1,X2,X0,X0)
      | ~ v1_funct_2(X0,X1,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(duplicate_literal_removal,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_funct_2(X1,X2,X0,X0)
      | ~ v1_funct_2(X0,X1,X2)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,X1,X2)
      | ~ v1_funct_1(X0) ) ),
    inference(condensation,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

fof(f98,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3) ),
    inference(backward_demodulation,[],[f45,f97])).

fof(f97,plain,(
    sK3 = k3_tmap_1(sK0,sK1,sK2,sK2,sK3) ),
    inference(subsumption_resolution,[],[f96,f34])).

fof(f34,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f96,plain,
    ( sK3 = k3_tmap_1(sK0,sK1,sK2,sK2,sK3)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f95,f35])).

fof(f35,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f95,plain,
    ( sK3 = k3_tmap_1(sK0,sK1,sK2,sK2,sK3)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f93,f36])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f93,plain,
    ( sK3 = k3_tmap_1(sK0,sK1,sK2,sK2,sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f92,f41])).

fof(f41,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f92,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,X0)
      | sK3 = k3_tmap_1(X0,sK1,sK2,sK2,sK3)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f91,f65])).

fof(f65,plain,(
    sK3 = k7_relat_1(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f64,f63])).

fof(f63,plain,(
    v4_relat_1(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f54,f44])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f64,plain,(
    ! [X0] :
      ( ~ v4_relat_1(sK3,X0)
      | sK3 = k7_relat_1(sK3,X0) ) ),
    inference(resolution,[],[f49,f61])).

fof(f61,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f53,f44])).

fof(f53,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f91,plain,(
    ! [X0] :
      ( k7_relat_1(sK3,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK2,sK2,sK3)
      | ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f90])).

fof(f90,plain,(
    ! [X0] :
      ( k7_relat_1(sK3,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK2,sK2,sK3)
      | ~ m1_pre_topc(sK2,X0)
      | ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f89,f75])).

fof(f75,plain,(
    m1_pre_topc(sK2,sK2) ),
    inference(subsumption_resolution,[],[f74,f35])).

fof(f74,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f73,f36])).

fof(f73,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f72,f41])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,X0)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(resolution,[],[f47,f57])).

fof(f57,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | k3_tmap_1(X1,sK1,sK2,X0,sK3) = k7_relat_1(sK3,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(forward_demodulation,[],[f88,f68])).

fof(f68,plain,(
    ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) ),
    inference(resolution,[],[f66,f44])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ) ),
    inference(resolution,[],[f56,f42])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | k3_tmap_1(X1,sK1,sK2,X0,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f87,f37])).

fof(f37,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | k3_tmap_1(X1,sK1,sK2,X0,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f86,f38])).

fof(f38,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | k3_tmap_1(X1,sK1,sK2,X0,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f85,f39])).

fof(f39,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | k3_tmap_1(X1,sK1,sK2,X0,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f84,f44])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X0,sK2)
      | k3_tmap_1(X1,sK1,sK2,X0,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f83,f43])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ m1_pre_topc(X0,X1)
      | k3_tmap_1(X3,X2,X1,X0,sK3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK3,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,X3)
      | ~ m1_pre_topc(X1,X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(resolution,[],[f46,f42])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f45,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(sK0,sK1,sK2,sK2,sK3)) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:41:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (21859)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.46  % (21877)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.46  % (21859)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f99,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(subsumption_resolution,[],[f98,f70])).
% 0.21/0.46  fof(f70,plain,(
% 0.21/0.46    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)),
% 0.21/0.46    inference(subsumption_resolution,[],[f69,f43])).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.21/0.46    inference(cnf_transformation,[],[f30])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    (((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(sK0,sK1,sK2,sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f29,f28,f27,f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(sK0,X1,X2,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ? [X1] : (? [X2] : (? [X3] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(sK0,X1,X2,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),X3,k3_tmap_1(sK0,sK1,X2,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ? [X2] : (? [X3] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),X3,k3_tmap_1(sK0,sK1,X2,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X3,k3_tmap_1(sK0,sK1,sK2,sK2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ? [X3] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X3,k3_tmap_1(sK0,sK1,sK2,sK2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X3)) => (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(sK0,sK1,sK2,sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK3))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,negated_conjecture,(
% 0.21/0.46    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))))))),
% 0.21/0.46    inference(negated_conjecture,[],[f9])).
% 0.21/0.46  fof(f9,conjecture,(
% 0.21/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tmap_1)).
% 0.21/0.46  fof(f69,plain,(
% 0.21/0.46    ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)),
% 0.21/0.46    inference(resolution,[],[f67,f44])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 0.21/0.46    inference(cnf_transformation,[],[f30])).
% 0.21/0.46  fof(f67,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK3,X0,X1) | r2_funct_2(X0,X1,sK3,sK3)) )),
% 0.21/0.46    inference(resolution,[],[f60,f42])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    v1_funct_1(sK3)),
% 0.21/0.46    inference(cnf_transformation,[],[f30])).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | r2_funct_2(X1,X2,X0,X0) | ~v1_funct_2(X0,X1,X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f59])).
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_funct_2(X1,X2,X0,X0) | ~v1_funct_2(X0,X1,X2) | ~v1_funct_1(X0) | ~v1_funct_2(X0,X1,X2) | ~v1_funct_1(X0)) )),
% 0.21/0.46    inference(condensation,[],[f55])).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.46    inference(flattening,[],[f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).
% 0.21/0.46  fof(f98,plain,(
% 0.21/0.46    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)),
% 0.21/0.46    inference(backward_demodulation,[],[f45,f97])).
% 0.21/0.46  fof(f97,plain,(
% 0.21/0.46    sK3 = k3_tmap_1(sK0,sK1,sK2,sK2,sK3)),
% 0.21/0.46    inference(subsumption_resolution,[],[f96,f34])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ~v2_struct_0(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f30])).
% 0.21/0.46  fof(f96,plain,(
% 0.21/0.46    sK3 = k3_tmap_1(sK0,sK1,sK2,sK2,sK3) | v2_struct_0(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f95,f35])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    v2_pre_topc(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f30])).
% 0.21/0.46  fof(f95,plain,(
% 0.21/0.46    sK3 = k3_tmap_1(sK0,sK1,sK2,sK2,sK3) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f93,f36])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    l1_pre_topc(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f30])).
% 0.21/0.46  fof(f93,plain,(
% 0.21/0.46    sK3 = k3_tmap_1(sK0,sK1,sK2,sK2,sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.46    inference(resolution,[],[f92,f41])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    m1_pre_topc(sK2,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f30])).
% 0.21/0.46  fof(f92,plain,(
% 0.21/0.46    ( ! [X0] : (~m1_pre_topc(sK2,X0) | sK3 = k3_tmap_1(X0,sK1,sK2,sK2,sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(forward_demodulation,[],[f91,f65])).
% 0.21/0.46  fof(f65,plain,(
% 0.21/0.46    sK3 = k7_relat_1(sK3,u1_struct_0(sK2))),
% 0.21/0.46    inference(resolution,[],[f64,f63])).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    v4_relat_1(sK3,u1_struct_0(sK2))),
% 0.21/0.46    inference(resolution,[],[f54,f44])).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.46    inference(pure_predicate_removal,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.46  fof(f64,plain,(
% 0.21/0.46    ( ! [X0] : (~v4_relat_1(sK3,X0) | sK3 = k7_relat_1(sK3,X0)) )),
% 0.21/0.46    inference(resolution,[],[f49,f61])).
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    v1_relat_1(sK3)),
% 0.21/0.46    inference(resolution,[],[f53,f44])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(flattening,[],[f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.46  fof(f91,plain,(
% 0.21/0.46    ( ! [X0] : (k7_relat_1(sK3,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK2,sK2,sK3) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f90])).
% 0.21/0.46  fof(f90,plain,(
% 0.21/0.46    ( ! [X0] : (k7_relat_1(sK3,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK2,sK2,sK3) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(resolution,[],[f89,f75])).
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    m1_pre_topc(sK2,sK2)),
% 0.21/0.46    inference(subsumption_resolution,[],[f74,f35])).
% 0.21/0.46  fof(f74,plain,(
% 0.21/0.46    m1_pre_topc(sK2,sK2) | ~v2_pre_topc(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f73,f36])).
% 0.21/0.46  fof(f73,plain,(
% 0.21/0.46    m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.46    inference(resolution,[],[f72,f41])).
% 0.21/0.46  fof(f72,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | m1_pre_topc(X0,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f71])).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    ( ! [X0,X1] : (m1_pre_topc(X0,X0) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 0.21/0.46    inference(resolution,[],[f47,f57])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.46    inference(equality_resolution,[],[f51])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.46    inference(cnf_transformation,[],[f33])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.46    inference(flattening,[],[f32])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.46    inference(nnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.46    inference(nnf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.46    inference(flattening,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,axiom,(
% 0.21/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.21/0.46  fof(f89,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | k3_tmap_1(X1,sK1,sK2,X0,sK3) = k7_relat_1(sK3,u1_struct_0(X0)) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.21/0.46    inference(forward_demodulation,[],[f88,f68])).
% 0.21/0.46  fof(f68,plain,(
% 0.21/0.46    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0)) )),
% 0.21/0.46    inference(resolution,[],[f66,f44])).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)) )),
% 0.21/0.46    inference(resolution,[],[f56,f42])).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.46    inference(flattening,[],[f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.21/0.46  fof(f88,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | k3_tmap_1(X1,sK1,sK2,X0,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0)) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f87,f37])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ~v2_struct_0(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f30])).
% 0.21/0.46  fof(f87,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | k3_tmap_1(X1,sK1,sK2,X0,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0)) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f86,f38])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    v2_pre_topc(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f30])).
% 0.21/0.46  fof(f86,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | k3_tmap_1(X1,sK1,sK2,X0,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0)) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f85,f39])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    l1_pre_topc(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f30])).
% 0.21/0.46  fof(f85,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | k3_tmap_1(X1,sK1,sK2,X0,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0)) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f84,f44])).
% 0.21/0.46  fof(f84,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK2) | k3_tmap_1(X1,sK1,sK2,X0,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0)) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.21/0.46    inference(resolution,[],[f83,f43])).
% 0.21/0.46  fof(f83,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (~v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X0,X1) | k3_tmap_1(X3,X2,X1,X0,sK3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK3,u1_struct_0(X0)) | ~m1_pre_topc(X0,X3) | ~m1_pre_topc(X1,X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) )),
% 0.21/0.46    inference(resolution,[],[f46,f42])).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(sK0,sK1,sK2,sK2,sK3))),
% 0.21/0.46    inference(cnf_transformation,[],[f30])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (21859)------------------------------
% 0.21/0.46  % (21859)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (21859)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (21859)Memory used [KB]: 6268
% 0.21/0.46  % (21859)Time elapsed: 0.055 s
% 0.21/0.46  % (21859)------------------------------
% 0.21/0.46  % (21859)------------------------------
% 0.21/0.47  % (21851)Success in time 0.107 s
%------------------------------------------------------------------------------
