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
% DateTime   : Thu Dec  3 13:22:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 443 expanded)
%              Number of leaves         :    9 ( 115 expanded)
%              Depth                    :   64
%              Number of atoms          :  584 (4137 expanded)
%              Number of equality atoms :    8 (  64 expanded)
%              Maximal formula depth    :   12 (   7 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f121,plain,(
    $false ),
    inference(subsumption_resolution,[],[f120,f30])).

fof(f30,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ v1_tdlat_3(sK0)
    & ! [X1] :
        ( ! [X2] :
            ( v5_pre_topc(X2,sK0,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            | ~ v1_funct_1(X2) )
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ~ v1_tdlat_3(X0)
        & ! [X1] :
            ( ! [X2] :
                ( v5_pre_topc(X2,X0,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                | ~ v1_funct_1(X2) )
            | ~ l1_pre_topc(X1)
            | ~ v2_pre_topc(X1)
            | v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ~ v1_tdlat_3(sK0)
      & ! [X1] :
          ( ! [X2] :
              ( v5_pre_topc(X2,sK0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ~ v1_tdlat_3(X0)
      & ! [X1] :
          ( ! [X2] :
              ( v5_pre_topc(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ~ v1_tdlat_3(X0)
      & ! [X1] :
          ( ! [X2] :
              ( v5_pre_topc(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( ! [X1] :
              ( ( l1_pre_topc(X1)
                & v2_pre_topc(X1)
                & ~ v2_struct_0(X1) )
             => ! [X2] :
                  ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                    & v1_funct_1(X2) )
                 => v5_pre_topc(X2,X0,X1) ) )
         => v1_tdlat_3(X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => v5_pre_topc(X2,X0,X1) ) )
       => v1_tdlat_3(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tex_2)).

fof(f120,plain,(
    ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f119,f31])).

fof(f31,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f119,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f118,f33])).

fof(f33,plain,(
    ~ v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f118,plain,
    ( v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f117,f39])).

fof(f39,plain,(
    ! [X0] :
      ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | ( ~ v3_pre_topc(sK1(X0),X0)
        & sK1(X0) = k1_tarski(sK2(X0))
        & m1_subset_1(sK2(X0),u1_struct_0(X0))
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f15,f27,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_pre_topc(X1,X0)
              & k1_tarski(X2) = X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ v3_pre_topc(sK1(X0),X0)
            & k1_tarski(X2) = sK1(X0)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(sK1(X0),X0)
          & k1_tarski(X2) = sK1(X0)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ v3_pre_topc(sK1(X0),X0)
        & sK1(X0) = k1_tarski(sK2(X0))
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | ? [X1] :
          ( ? [X2] :
              ( ~ v3_pre_topc(X1,X0)
              & k1_tarski(X2) = X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | ? [X1] :
          ( ? [X2] :
              ( ~ v3_pre_topc(X1,X0)
              & k1_tarski(X2) = X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k1_tarski(X2) = X1
                 => v3_pre_topc(X1,X0) ) ) )
       => v1_tdlat_3(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tdlat_3)).

fof(f117,plain,(
    ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f116,f29])).

fof(f29,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f116,plain,
    ( ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f115,f30])).

fof(f115,plain,
    ( ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f111,f31])).

fof(f111,plain,
    ( ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f109,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(f109,plain,(
    ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) ),
    inference(subsumption_resolution,[],[f108,f30])).

fof(f108,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f107,f31])).

fof(f107,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f106,f33])).

fof(f106,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))
    | v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f105,f39])).

fof(f105,plain,
    ( ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) ),
    inference(subsumption_resolution,[],[f104,f29])).

fof(f104,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))
    | ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f103,f30])).

fof(f103,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))
    | ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f99,f31])).

fof(f99,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))
    | ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f97,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f97,plain,
    ( ~ v1_funct_1(k7_tmap_1(sK0,sK1(sK0)))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) ),
    inference(subsumption_resolution,[],[f96,f30])).

fof(f96,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1(sK0)))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f95,f31])).

fof(f95,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f94,f33])).

fof(f94,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1(sK0)))
    | v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f93,f39])).

fof(f93,plain,
    ( ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1(sK0))) ),
    inference(subsumption_resolution,[],[f92,f29])).

fof(f92,plain,
    ( ~ v1_funct_1(k7_tmap_1(sK0,sK1(sK0)))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))
    | ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f91,f30])).

fof(f91,plain,
    ( ~ v1_funct_1(k7_tmap_1(sK0,sK1(sK0)))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))
    | ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f90,f31])).

fof(f90,plain,
    ( ~ v1_funct_1(k7_tmap_1(sK0,sK1(sK0)))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))
    | ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f88,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f88,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1(sK0)))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) ),
    inference(subsumption_resolution,[],[f87,f30])).

fof(f87,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1(sK0)))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f86,f31])).

fof(f86,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1(sK0)))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f85,f33])).

fof(f85,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1(sK0)))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))
    | v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f84,f39])).

fof(f84,plain,
    ( ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1(sK0)))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))) ),
    inference(subsumption_resolution,[],[f83,f29])).

fof(f83,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1(sK0)))
    | ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f82,f30])).

fof(f82,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1(sK0)))
    | ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f81,f31])).

fof(f81,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1(sK0)))
    | ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f80,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_tmap_1)).

fof(f80,plain,
    ( v2_struct_0(k6_tmap_1(sK0,sK1(sK0)))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1(sK0))) ),
    inference(subsumption_resolution,[],[f79,f30])).

fof(f79,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))
    | v2_struct_0(k6_tmap_1(sK0,sK1(sK0)))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1(sK0)))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f78,f31])).

fof(f78,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))
    | v2_struct_0(k6_tmap_1(sK0,sK1(sK0)))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f77,f33])).

fof(f77,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))
    | v2_struct_0(k6_tmap_1(sK0,sK1(sK0)))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1(sK0)))
    | v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f76,f39])).

fof(f76,plain,
    ( ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))
    | v2_struct_0(k6_tmap_1(sK0,sK1(sK0)))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1(sK0))) ),
    inference(subsumption_resolution,[],[f75,f29])).

fof(f75,plain,
    ( ~ v1_funct_1(k7_tmap_1(sK0,sK1(sK0)))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))
    | v2_struct_0(k6_tmap_1(sK0,sK1(sK0)))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))
    | ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f74,f30])).

fof(f74,plain,
    ( ~ v1_funct_1(k7_tmap_1(sK0,sK1(sK0)))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))
    | v2_struct_0(k6_tmap_1(sK0,sK1(sK0)))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))
    | ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f73,f31])).

fof(f73,plain,
    ( ~ v1_funct_1(k7_tmap_1(sK0,sK1(sK0)))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))
    | v2_struct_0(k6_tmap_1(sK0,sK1(sK0)))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))
    | ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f72,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f72,plain,
    ( ~ v2_pre_topc(k6_tmap_1(sK0,sK1(sK0)))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1(sK0)))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))
    | v2_struct_0(k6_tmap_1(sK0,sK1(sK0)))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) ),
    inference(subsumption_resolution,[],[f71,f30])).

fof(f71,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1(sK0)))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1(sK0)))
    | v2_struct_0(k6_tmap_1(sK0,sK1(sK0)))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f70,f31])).

fof(f70,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1(sK0)))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1(sK0)))
    | v2_struct_0(k6_tmap_1(sK0,sK1(sK0)))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f69,f33])).

fof(f69,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1(sK0)))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1(sK0)))
    | v2_struct_0(k6_tmap_1(sK0,sK1(sK0)))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))
    | v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f68,f39])).

fof(f68,plain,
    ( ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1(sK0)))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1(sK0)))
    | v2_struct_0(k6_tmap_1(sK0,sK1(sK0)))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) ),
    inference(subsumption_resolution,[],[f67,f29])).

fof(f67,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1(sK0)))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1(sK0)))
    | v2_struct_0(k6_tmap_1(sK0,sK1(sK0)))
    | ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f66,f30])).

fof(f66,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1(sK0)))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1(sK0)))
    | v2_struct_0(k6_tmap_1(sK0,sK1(sK0)))
    | ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f65,f31])).

fof(f65,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1(sK0)))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1(sK0)))
    | v2_struct_0(k6_tmap_1(sK0,sK1(sK0)))
    | ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f61,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(f61,plain,
    ( ~ l1_pre_topc(k6_tmap_1(sK0,sK1(sK0)))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1(sK0)))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1(sK0)))
    | v2_struct_0(k6_tmap_1(sK0,sK1(sK0))) ),
    inference(duplicate_literal_removal,[],[f60])).

fof(f60,plain,
    ( ~ v1_funct_1(k7_tmap_1(sK0,sK1(sK0)))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1(sK0)))
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1(sK0)))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1(sK0)))
    | v2_struct_0(k6_tmap_1(sK0,sK1(sK0))) ),
    inference(resolution,[],[f58,f32])).

fof(f32,plain,(
    ! [X2,X1] :
      ( v5_pre_topc(X2,sK0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f58,plain,
    ( ~ v5_pre_topc(k7_tmap_1(sK0,sK1(sK0)),sK0,k6_tmap_1(sK0,sK1(sK0)))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1(sK0))) ),
    inference(subsumption_resolution,[],[f57,f29])).

fof(f57,plain,
    ( ~ v1_funct_1(k7_tmap_1(sK0,sK1(sK0)))
    | v2_struct_0(sK0)
    | ~ v5_pre_topc(k7_tmap_1(sK0,sK1(sK0)),sK0,k6_tmap_1(sK0,sK1(sK0))) ),
    inference(subsumption_resolution,[],[f56,f30])).

fof(f56,plain,
    ( ~ v1_funct_1(k7_tmap_1(sK0,sK1(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v5_pre_topc(k7_tmap_1(sK0,sK1(sK0)),sK0,k6_tmap_1(sK0,sK1(sK0))) ),
    inference(subsumption_resolution,[],[f55,f31])).

fof(f55,plain,
    ( ~ v1_funct_1(k7_tmap_1(sK0,sK1(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v5_pre_topc(k7_tmap_1(sK0,sK1(sK0)),sK0,k6_tmap_1(sK0,sK1(sK0))) ),
    inference(resolution,[],[f54,f33])).

fof(f54,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | ~ v1_funct_1(k7_tmap_1(X0,sK1(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v5_pre_topc(k7_tmap_1(X0,sK1(X0)),X0,k6_tmap_1(X0,sK1(X0))) ) ),
    inference(subsumption_resolution,[],[f53,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(sK1(X0),X0)
      | v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v5_pre_topc(k7_tmap_1(X0,sK1(X0)),X0,k6_tmap_1(X0,sK1(X0)))
      | ~ v1_funct_1(k7_tmap_1(X0,sK1(X0)))
      | v3_pre_topc(sK1(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_tdlat_3(X0) ) ),
    inference(duplicate_literal_removal,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v5_pre_topc(k7_tmap_1(X0,sK1(X0)),X0,k6_tmap_1(X0,sK1(X0)))
      | ~ v1_funct_1(k7_tmap_1(X0,sK1(X0)))
      | v3_pre_topc(sK1(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f51,f39])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
      | ~ v1_funct_1(k7_tmap_1(X0,X1))
      | v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f50,f46])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
      | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f38,f47])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
      | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              | ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              | ~ v1_funct_1(k7_tmap_1(X0,X1)) )
            & ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
                & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
                & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
                & v1_funct_1(k7_tmap_1(X0,X1)) )
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              | ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              | ~ v1_funct_1(k7_tmap_1(X0,X1)) )
            & ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
                & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
                & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
                & v1_funct_1(k7_tmap_1(X0,X1)) )
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_tmap_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:19:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (29906)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.46  % (29914)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.46  % (29914)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f121,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(subsumption_resolution,[],[f120,f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    v2_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ~v1_tdlat_3(sK0) & ! [X1] : (! [X2] : (v5_pre_topc(X2,sK0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ? [X0] : (~v1_tdlat_3(X0) & ! [X1] : (! [X2] : (v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (~v1_tdlat_3(sK0) & ! [X1] : (! [X2] : (v5_pre_topc(X2,sK0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ? [X0] : (~v1_tdlat_3(X0) & ! [X1] : (! [X2] : (v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ? [X0] : ((~v1_tdlat_3(X0) & ! [X1] : (! [X2] : (v5_pre_topc(X2,X0,X1) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => v5_pre_topc(X2,X0,X1))) => v1_tdlat_3(X0)))),
% 0.21/0.47    inference(negated_conjecture,[],[f6])).
% 0.21/0.47  fof(f6,conjecture,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => v5_pre_topc(X2,X0,X1))) => v1_tdlat_3(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tex_2)).
% 0.21/0.47  fof(f120,plain,(
% 0.21/0.47    ~v2_pre_topc(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f119,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    l1_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f119,plain,(
% 0.21/0.47    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f118,f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ~v1_tdlat_3(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f118,plain,(
% 0.21/0.47    v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.47    inference(resolution,[],[f117,f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X0] : (m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) | v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ! [X0] : (v1_tdlat_3(X0) | ((~v3_pre_topc(sK1(X0),X0) & sK1(X0) = k1_tarski(sK2(X0)) & m1_subset_1(sK2(X0),u1_struct_0(X0))) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f15,f27,f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X0] : (? [X1] : (? [X2] : (~v3_pre_topc(X1,X0) & k1_tarski(X2) = X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~v3_pre_topc(sK1(X0),X0) & k1_tarski(X2) = sK1(X0) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ! [X0] : (? [X2] : (~v3_pre_topc(sK1(X0),X0) & k1_tarski(X2) = sK1(X0) & m1_subset_1(X2,u1_struct_0(X0))) => (~v3_pre_topc(sK1(X0),X0) & sK1(X0) = k1_tarski(sK2(X0)) & m1_subset_1(sK2(X0),u1_struct_0(X0))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0] : (v1_tdlat_3(X0) | ? [X1] : (? [X2] : (~v3_pre_topc(X1,X0) & k1_tarski(X2) = X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0] : ((v1_tdlat_3(X0) | ? [X1] : (? [X2] : ((~v3_pre_topc(X1,X0) & k1_tarski(X2) = X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k1_tarski(X2) = X1 => v3_pre_topc(X1,X0)))) => v1_tdlat_3(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tdlat_3)).
% 0.21/0.47  fof(f117,plain,(
% 0.21/0.47    ~m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.47    inference(subsumption_resolution,[],[f116,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ~v2_struct_0(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f116,plain,(
% 0.21/0.47    ~m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f115,f30])).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    ~m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f111,f31])).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    ~m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.47    inference(resolution,[],[f109,f47])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))),
% 0.21/0.47    inference(subsumption_resolution,[],[f108,f30])).
% 0.21/0.47  fof(f108,plain,(
% 0.21/0.47    ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) | ~v2_pre_topc(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f107,f31])).
% 0.21/0.47  fof(f107,plain,(
% 0.21/0.47    ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f106,f33])).
% 0.21/0.47  fof(f106,plain,(
% 0.21/0.47    ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) | v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.47    inference(resolution,[],[f105,f39])).
% 0.21/0.47  fof(f105,plain,(
% 0.21/0.47    ~m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))),
% 0.21/0.47    inference(subsumption_resolution,[],[f104,f29])).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) | ~m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f103,f30])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) | ~m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f99,f31])).
% 0.21/0.47  fof(f99,plain,(
% 0.21/0.47    ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) | ~m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.47    inference(resolution,[],[f97,f45])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f97,plain,(
% 0.21/0.47    ~v1_funct_1(k7_tmap_1(sK0,sK1(sK0))) | ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))),
% 0.21/0.47    inference(subsumption_resolution,[],[f96,f30])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) | ~v1_funct_1(k7_tmap_1(sK0,sK1(sK0))) | ~v2_pre_topc(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f95,f31])).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) | ~v1_funct_1(k7_tmap_1(sK0,sK1(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f94,f33])).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) | ~v1_funct_1(k7_tmap_1(sK0,sK1(sK0))) | v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.47    inference(resolution,[],[f93,f39])).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    ~m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) | ~v1_funct_1(k7_tmap_1(sK0,sK1(sK0)))),
% 0.21/0.47    inference(subsumption_resolution,[],[f92,f29])).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    ~v1_funct_1(k7_tmap_1(sK0,sK1(sK0))) | ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) | ~m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f91,f30])).
% 0.21/0.47  fof(f91,plain,(
% 0.21/0.47    ~v1_funct_1(k7_tmap_1(sK0,sK1(sK0))) | ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) | ~m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f90,f31])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    ~v1_funct_1(k7_tmap_1(sK0,sK1(sK0))) | ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) | ~m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.47    inference(resolution,[],[f88,f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    ~v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))) | ~v1_funct_1(k7_tmap_1(sK0,sK1(sK0))) | ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))),
% 0.21/0.47    inference(subsumption_resolution,[],[f87,f30])).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) | ~v1_funct_1(k7_tmap_1(sK0,sK1(sK0))) | ~v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))) | ~v2_pre_topc(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f86,f31])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) | ~v1_funct_1(k7_tmap_1(sK0,sK1(sK0))) | ~v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f85,f33])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) | ~v1_funct_1(k7_tmap_1(sK0,sK1(sK0))) | ~v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))) | v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.47    inference(resolution,[],[f84,f39])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    ~m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) | ~v1_funct_1(k7_tmap_1(sK0,sK1(sK0))) | ~v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))),
% 0.21/0.47    inference(subsumption_resolution,[],[f83,f29])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    ~v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))) | ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) | ~v1_funct_1(k7_tmap_1(sK0,sK1(sK0))) | ~m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f82,f30])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    ~v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))) | ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) | ~v1_funct_1(k7_tmap_1(sK0,sK1(sK0))) | ~m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f81,f31])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    ~v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))) | ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) | ~v1_funct_1(k7_tmap_1(sK0,sK1(sK0))) | ~m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.47    inference(resolution,[],[f80,f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v2_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1] : ((v2_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1] : ((v2_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))))),
% 0.21/0.47    inference(pure_predicate_removal,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_tmap_1)).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    v2_struct_0(k6_tmap_1(sK0,sK1(sK0))) | ~v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))) | ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) | ~v1_funct_1(k7_tmap_1(sK0,sK1(sK0)))),
% 0.21/0.47    inference(subsumption_resolution,[],[f79,f30])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    ~v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))) | v2_struct_0(k6_tmap_1(sK0,sK1(sK0))) | ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) | ~v1_funct_1(k7_tmap_1(sK0,sK1(sK0))) | ~v2_pre_topc(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f78,f31])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    ~v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))) | v2_struct_0(k6_tmap_1(sK0,sK1(sK0))) | ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) | ~v1_funct_1(k7_tmap_1(sK0,sK1(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f77,f33])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    ~v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))) | v2_struct_0(k6_tmap_1(sK0,sK1(sK0))) | ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) | ~v1_funct_1(k7_tmap_1(sK0,sK1(sK0))) | v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.47    inference(resolution,[],[f76,f39])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    ~m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))) | v2_struct_0(k6_tmap_1(sK0,sK1(sK0))) | ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) | ~v1_funct_1(k7_tmap_1(sK0,sK1(sK0)))),
% 0.21/0.47    inference(subsumption_resolution,[],[f75,f29])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    ~v1_funct_1(k7_tmap_1(sK0,sK1(sK0))) | ~v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))) | v2_struct_0(k6_tmap_1(sK0,sK1(sK0))) | ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) | ~m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f74,f30])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    ~v1_funct_1(k7_tmap_1(sK0,sK1(sK0))) | ~v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))) | v2_struct_0(k6_tmap_1(sK0,sK1(sK0))) | ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) | ~m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f73,f31])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    ~v1_funct_1(k7_tmap_1(sK0,sK1(sK0))) | ~v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))) | v2_struct_0(k6_tmap_1(sK0,sK1(sK0))) | ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) | ~m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.47    inference(resolution,[],[f72,f44])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v2_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    ~v2_pre_topc(k6_tmap_1(sK0,sK1(sK0))) | ~v1_funct_1(k7_tmap_1(sK0,sK1(sK0))) | ~v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))) | v2_struct_0(k6_tmap_1(sK0,sK1(sK0))) | ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))),
% 0.21/0.47    inference(subsumption_resolution,[],[f71,f30])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    ~v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))) | ~v1_funct_1(k7_tmap_1(sK0,sK1(sK0))) | ~v2_pre_topc(k6_tmap_1(sK0,sK1(sK0))) | v2_struct_0(k6_tmap_1(sK0,sK1(sK0))) | ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) | ~v2_pre_topc(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f70,f31])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    ~v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))) | ~v1_funct_1(k7_tmap_1(sK0,sK1(sK0))) | ~v2_pre_topc(k6_tmap_1(sK0,sK1(sK0))) | v2_struct_0(k6_tmap_1(sK0,sK1(sK0))) | ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f69,f33])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    ~v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))) | ~v1_funct_1(k7_tmap_1(sK0,sK1(sK0))) | ~v2_pre_topc(k6_tmap_1(sK0,sK1(sK0))) | v2_struct_0(k6_tmap_1(sK0,sK1(sK0))) | ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) | v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.47    inference(resolution,[],[f68,f39])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    ~m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))) | ~v1_funct_1(k7_tmap_1(sK0,sK1(sK0))) | ~v2_pre_topc(k6_tmap_1(sK0,sK1(sK0))) | v2_struct_0(k6_tmap_1(sK0,sK1(sK0))) | ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0))))))),
% 0.21/0.47    inference(subsumption_resolution,[],[f67,f29])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) | ~v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))) | ~v1_funct_1(k7_tmap_1(sK0,sK1(sK0))) | ~v2_pre_topc(k6_tmap_1(sK0,sK1(sK0))) | v2_struct_0(k6_tmap_1(sK0,sK1(sK0))) | ~m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f66,f30])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) | ~v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))) | ~v1_funct_1(k7_tmap_1(sK0,sK1(sK0))) | ~v2_pre_topc(k6_tmap_1(sK0,sK1(sK0))) | v2_struct_0(k6_tmap_1(sK0,sK1(sK0))) | ~m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f65,f31])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) | ~v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))) | ~v1_funct_1(k7_tmap_1(sK0,sK1(sK0))) | ~v2_pre_topc(k6_tmap_1(sK0,sK1(sK0))) | v2_struct_0(k6_tmap_1(sK0,sK1(sK0))) | ~m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.47    inference(resolution,[],[f61,f49])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ( ! [X0,X1] : (l1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))))),
% 0.21/0.47    inference(pure_predicate_removal,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    ~l1_pre_topc(k6_tmap_1(sK0,sK1(sK0))) | ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) | ~v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))) | ~v1_funct_1(k7_tmap_1(sK0,sK1(sK0))) | ~v2_pre_topc(k6_tmap_1(sK0,sK1(sK0))) | v2_struct_0(k6_tmap_1(sK0,sK1(sK0)))),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f60])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    ~v1_funct_1(k7_tmap_1(sK0,sK1(sK0))) | ~m1_subset_1(k7_tmap_1(sK0,sK1(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))))) | ~v1_funct_2(k7_tmap_1(sK0,sK1(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1(sK0)))) | ~v1_funct_1(k7_tmap_1(sK0,sK1(sK0))) | ~l1_pre_topc(k6_tmap_1(sK0,sK1(sK0))) | ~v2_pre_topc(k6_tmap_1(sK0,sK1(sK0))) | v2_struct_0(k6_tmap_1(sK0,sK1(sK0)))),
% 0.21/0.47    inference(resolution,[],[f58,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X2,X1] : (v5_pre_topc(X2,sK0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    ~v5_pre_topc(k7_tmap_1(sK0,sK1(sK0)),sK0,k6_tmap_1(sK0,sK1(sK0))) | ~v1_funct_1(k7_tmap_1(sK0,sK1(sK0)))),
% 0.21/0.47    inference(subsumption_resolution,[],[f57,f29])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    ~v1_funct_1(k7_tmap_1(sK0,sK1(sK0))) | v2_struct_0(sK0) | ~v5_pre_topc(k7_tmap_1(sK0,sK1(sK0)),sK0,k6_tmap_1(sK0,sK1(sK0)))),
% 0.21/0.47    inference(subsumption_resolution,[],[f56,f30])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ~v1_funct_1(k7_tmap_1(sK0,sK1(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~v5_pre_topc(k7_tmap_1(sK0,sK1(sK0)),sK0,k6_tmap_1(sK0,sK1(sK0)))),
% 0.21/0.47    inference(subsumption_resolution,[],[f55,f31])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ~v1_funct_1(k7_tmap_1(sK0,sK1(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~v5_pre_topc(k7_tmap_1(sK0,sK1(sK0)),sK0,k6_tmap_1(sK0,sK1(sK0)))),
% 0.21/0.47    inference(resolution,[],[f54,f33])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ( ! [X0] : (v1_tdlat_3(X0) | ~v1_funct_1(k7_tmap_1(X0,sK1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v5_pre_topc(k7_tmap_1(X0,sK1(X0)),X0,k6_tmap_1(X0,sK1(X0)))) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f53,f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X0] : (~v3_pre_topc(sK1(X0),X0) | v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f28])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    ( ! [X0] : (~v5_pre_topc(k7_tmap_1(X0,sK1(X0)),X0,k6_tmap_1(X0,sK1(X0))) | ~v1_funct_1(k7_tmap_1(X0,sK1(X0))) | v3_pre_topc(sK1(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v1_tdlat_3(X0)) )),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f52])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    ( ! [X0] : (~v5_pre_topc(k7_tmap_1(X0,sK1(X0)),X0,k6_tmap_1(X0,sK1(X0))) | ~v1_funct_1(k7_tmap_1(X0,sK1(X0))) | v3_pre_topc(sK1(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.47    inference(resolution,[],[f51,f39])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_1(k7_tmap_1(X0,X1)) | v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f50,f46])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f38,f47])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1))) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | (~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1)))) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_tmap_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (29914)------------------------------
% 0.21/0.47  % (29914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (29914)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (29914)Memory used [KB]: 6140
% 0.21/0.47  % (29914)Time elapsed: 0.061 s
% 0.21/0.47  % (29914)------------------------------
% 0.21/0.47  % (29914)------------------------------
% 0.21/0.47  % (29894)Success in time 0.117 s
%------------------------------------------------------------------------------
