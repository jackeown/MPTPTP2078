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
% DateTime   : Thu Dec  3 13:18:25 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 569 expanded)
%              Number of leaves         :   20 ( 253 expanded)
%              Depth                    :   23
%              Number of atoms          :  444 (6233 expanded)
%              Number of equality atoms :   52 ( 620 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f384,plain,(
    $false ),
    inference(resolution,[],[f337,f194])).

fof(f194,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f193,f139])).

fof(f139,plain,(
    ! [X7] : v1_relat_1(k7_relat_1(sK3,X7)) ),
    inference(resolution,[],[f125,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f125,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f120,f64])).

fof(f64,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f120,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(resolution,[],[f55,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
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

fof(f55,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4)
    & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f18,f42,f41,f40,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)
                        & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
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
                  ( ? [X4] :
                      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X3,X2),X4)
                      & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X1))
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

fof(f39,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X3,X2),X4)
                    & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X1))
                & v1_funct_1(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X3,X2),X4)
                  & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4),u1_struct_0(X2))
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
              & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK1))
              & v1_funct_1(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X3,X2),X4)
                & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4),u1_struct_0(X2))
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
            & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK1))
            & v1_funct_1(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X3,sK2),X4)
              & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4),u1_struct_0(sK2))
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X3,sK2),X4)
            & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4),u1_struct_0(sK2))
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),X4)
          & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X4),u1_struct_0(sK2))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X4] :
        ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),X4)
        & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X4),u1_struct_0(sK2))
        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4)
      & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2))
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)
                      & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)
                      & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X3) )
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ( r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
                         => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
                       => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tmap_1)).

fof(f193,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK1))
    | ~ v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f192,f141])).

fof(f141,plain,(
    ! [X9] : r1_tarski(k1_relat_1(k7_relat_1(sK3,X9)),X9) ),
    inference(resolution,[],[f125,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f192,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK1))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK2))
    | ~ v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) ),
    inference(resolution,[],[f190,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f190,plain,(
    ~ m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f189,f132])).

fof(f132,plain,(
    k10_relat_1(sK3,sK4) = k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) ),
    inference(subsumption_resolution,[],[f131,f125])).

fof(f131,plain,
    ( k10_relat_1(sK3,sK4) = k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f126,f53])).

fof(f53,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f126,plain,
    ( k10_relat_1(sK3,sK4) = k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f123,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)
      | ~ r1_tarski(k10_relat_1(X0,X2),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)
          | ~ r1_tarski(k10_relat_1(X0,X2),X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)
          | ~ r1_tarski(k10_relat_1(X0,X2),X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

fof(f123,plain,(
    r1_tarski(k10_relat_1(sK3,sK4),u1_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f57,f117])).

fof(f117,plain,(
    ! [X2] : k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X2) = k10_relat_1(sK3,X2) ),
    inference(resolution,[],[f55,f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f57,plain,(
    r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f43])).

fof(f189,plain,
    ( k10_relat_1(sK3,sK4) != k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4)
    | ~ m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f187,f186])).

fof(f186,plain,(
    k2_tmap_1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f122,f52])).

fof(f52,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f122,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | k2_tmap_1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0)) ) ),
    inference(backward_demodulation,[],[f114,f121])).

fof(f121,plain,(
    ! [X1] : k7_relat_1(sK3,X1) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X1) ),
    inference(subsumption_resolution,[],[f116,f53])).

fof(f116,plain,(
    ! [X1] :
      ( k7_relat_1(sK3,X1) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X1)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f55,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f114,plain,(
    ! [X0] :
      ( k2_tmap_1(sK0,sK1,sK3,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f113,f45])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f113,plain,(
    ! [X0] :
      ( k2_tmap_1(sK0,sK1,sK3,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f112,f46])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f112,plain,(
    ! [X0] :
      ( k2_tmap_1(sK0,sK1,sK3,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f111,f47])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f111,plain,(
    ! [X0] :
      ( k2_tmap_1(sK0,sK1,sK3,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f110,f48])).

fof(f48,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f110,plain,(
    ! [X0] :
      ( k2_tmap_1(sK0,sK1,sK3,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f109,f49])).

fof(f49,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f109,plain,(
    ! [X0] :
      ( k2_tmap_1(sK0,sK1,sK3,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f108,f50])).

fof(f50,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f108,plain,(
    ! [X0] :
      ( k2_tmap_1(sK0,sK1,sK3,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f107,f53])).

fof(f107,plain,(
    ! [X0] :
      ( k2_tmap_1(sK0,sK1,sK3,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK0)
      | ~ v1_funct_1(sK3)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f106,f55])).

fof(f106,plain,(
    ! [X0] :
      ( k2_tmap_1(sK0,sK1,sK3,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v1_funct_1(sK3)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f54,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f54,plain,(
    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f187,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | k10_relat_1(sK3,sK4) != k10_relat_1(k2_tmap_1(sK0,sK1,sK3,sK2),sK4) ),
    inference(backward_demodulation,[],[f146,f186])).

fof(f146,plain,
    ( k10_relat_1(sK3,sK4) != k10_relat_1(k2_tmap_1(sK0,sK1,sK3,sK2),sK4)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(superposition,[],[f124,f74])).

fof(f124,plain,(
    k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) != k10_relat_1(sK3,sK4) ),
    inference(backward_demodulation,[],[f58,f117])).

fof(f58,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f337,plain,(
    ! [X5] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X5)),u1_struct_0(sK1)) ),
    inference(resolution,[],[f182,f174])).

fof(f174,plain,(
    ! [X5] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X5)),k2_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f173,f139])).

fof(f173,plain,(
    ! [X5] :
      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X5)),k2_relat_1(sK3))
      | ~ v1_relat_1(k7_relat_1(sK3,X5)) ) ),
    inference(subsumption_resolution,[],[f170,f125])).

fof(f170,plain,(
    ! [X5] :
      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X5)),k2_relat_1(sK3))
      | ~ v1_relat_1(sK3)
      | ~ v1_relat_1(k7_relat_1(sK3,X5)) ) ),
    inference(resolution,[],[f140,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f140,plain,(
    ! [X8] : r1_tarski(k7_relat_1(sK3,X8),sK3) ),
    inference(resolution,[],[f125,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f182,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k2_relat_1(sK3))
      | r1_tarski(X2,u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f148,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f148,plain,(
    r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f147,f125])).

fof(f147,plain,
    ( r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f119,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f119,plain,(
    v5_relat_1(sK3,u1_struct_0(sK1)) ),
    inference(resolution,[],[f55,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:38:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (15688)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.48  % (15696)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.51  % (15676)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.52  % (15685)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.52  % (15677)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.52  % (15685)Refutation not found, incomplete strategy% (15685)------------------------------
% 0.22/0.52  % (15685)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (15685)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (15685)Memory used [KB]: 10746
% 0.22/0.52  % (15685)Time elapsed: 0.087 s
% 0.22/0.52  % (15685)------------------------------
% 0.22/0.52  % (15685)------------------------------
% 0.22/0.52  % (15683)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.53  % (15686)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.53  % (15678)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.53  % (15697)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 1.34/0.54  % (15679)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 1.34/0.54  % (15692)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 1.34/0.54  % (15683)Refutation not found, incomplete strategy% (15683)------------------------------
% 1.34/0.54  % (15683)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (15683)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (15683)Memory used [KB]: 10618
% 1.34/0.54  % (15683)Time elapsed: 0.103 s
% 1.34/0.54  % (15683)------------------------------
% 1.34/0.54  % (15683)------------------------------
% 1.34/0.54  % (15687)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 1.34/0.55  % (15684)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 1.48/0.55  % (15689)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 1.48/0.56  % (15686)Refutation found. Thanks to Tanya!
% 1.48/0.56  % SZS status Theorem for theBenchmark
% 1.48/0.56  % SZS output start Proof for theBenchmark
% 1.48/0.56  fof(f384,plain,(
% 1.48/0.56    $false),
% 1.48/0.56    inference(resolution,[],[f337,f194])).
% 1.48/0.56  fof(f194,plain,(
% 1.48/0.56    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK1))),
% 1.48/0.56    inference(subsumption_resolution,[],[f193,f139])).
% 1.48/0.56  fof(f139,plain,(
% 1.48/0.56    ( ! [X7] : (v1_relat_1(k7_relat_1(sK3,X7))) )),
% 1.48/0.56    inference(resolution,[],[f125,f65])).
% 1.48/0.56  fof(f65,plain,(
% 1.48/0.56    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f26])).
% 1.48/0.56  fof(f26,plain,(
% 1.48/0.56    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.48/0.56    inference(ennf_transformation,[],[f4])).
% 1.48/0.56  fof(f4,axiom,(
% 1.48/0.56    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.48/0.56  fof(f125,plain,(
% 1.48/0.56    v1_relat_1(sK3)),
% 1.48/0.56    inference(subsumption_resolution,[],[f120,f64])).
% 1.48/0.56  fof(f64,plain,(
% 1.48/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.48/0.56    inference(cnf_transformation,[],[f5])).
% 1.48/0.56  fof(f5,axiom,(
% 1.48/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.48/0.56  fof(f120,plain,(
% 1.48/0.56    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))),
% 1.48/0.56    inference(resolution,[],[f55,f61])).
% 1.48/0.56  fof(f61,plain,(
% 1.48/0.56    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f21])).
% 1.48/0.56  fof(f21,plain,(
% 1.48/0.56    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.48/0.56    inference(ennf_transformation,[],[f2])).
% 1.48/0.56  fof(f2,axiom,(
% 1.48/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.48/0.56  fof(f55,plain,(
% 1.48/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.48/0.56    inference(cnf_transformation,[],[f43])).
% 1.48/0.56  fof(f43,plain,(
% 1.48/0.56    ((((k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.48/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f18,f42,f41,f40,f39,f38])).
% 1.48/0.56  fof(f38,plain,(
% 1.48/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.48/0.56    introduced(choice_axiom,[])).
% 1.48/0.56  fof(f39,plain,(
% 1.48/0.56    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.48/0.56    introduced(choice_axiom,[])).
% 1.48/0.56  fof(f40,plain,(
% 1.48/0.56    ? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X3,sK2),X4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4),u1_struct_0(sK2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 1.48/0.56    introduced(choice_axiom,[])).
% 1.48/0.56  fof(f41,plain,(
% 1.48/0.56    ? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X3,sK2),X4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4),u1_struct_0(sK2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X3)) => (? [X4] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),X4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X4),u1_struct_0(sK2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK3))),
% 1.48/0.56    introduced(choice_axiom,[])).
% 1.48/0.56  fof(f42,plain,(
% 1.48/0.56    ? [X4] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),X4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X4),u1_struct_0(sK2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) => (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))))),
% 1.48/0.56    introduced(choice_axiom,[])).
% 1.48/0.56  fof(f18,plain,(
% 1.48/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.48/0.56    inference(flattening,[],[f17])).
% 1.48/0.56  fof(f17,plain,(
% 1.48/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.48/0.56    inference(ennf_transformation,[],[f16])).
% 1.48/0.56  fof(f16,negated_conjecture,(
% 1.48/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)))))))),
% 1.48/0.56    inference(negated_conjecture,[],[f15])).
% 1.48/0.56  fof(f15,conjecture,(
% 1.48/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)))))))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tmap_1)).
% 1.48/0.56  fof(f193,plain,(
% 1.48/0.56    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK1)) | ~v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))),
% 1.48/0.56    inference(subsumption_resolution,[],[f192,f141])).
% 1.48/0.56  fof(f141,plain,(
% 1.48/0.56    ( ! [X9] : (r1_tarski(k1_relat_1(k7_relat_1(sK3,X9)),X9)) )),
% 1.48/0.56    inference(resolution,[],[f125,f67])).
% 1.48/0.56  fof(f67,plain,(
% 1.48/0.56    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f28])).
% 1.48/0.56  fof(f28,plain,(
% 1.48/0.56    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.48/0.56    inference(ennf_transformation,[],[f7])).
% 1.48/0.56  fof(f7,axiom,(
% 1.48/0.56    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 1.48/0.56  fof(f192,plain,(
% 1.48/0.56    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK1)) | ~r1_tarski(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK2)) | ~v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))),
% 1.48/0.56    inference(resolution,[],[f190,f70])).
% 1.48/0.56  fof(f70,plain,(
% 1.48/0.56    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f31])).
% 1.48/0.56  fof(f31,plain,(
% 1.48/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.48/0.56    inference(flattening,[],[f30])).
% 1.48/0.56  fof(f30,plain,(
% 1.48/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.48/0.56    inference(ennf_transformation,[],[f11])).
% 1.48/0.56  fof(f11,axiom,(
% 1.48/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 1.48/0.56  fof(f190,plain,(
% 1.48/0.56    ~m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 1.48/0.56    inference(subsumption_resolution,[],[f189,f132])).
% 1.48/0.56  fof(f132,plain,(
% 1.48/0.56    k10_relat_1(sK3,sK4) = k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4)),
% 1.48/0.56    inference(subsumption_resolution,[],[f131,f125])).
% 1.48/0.56  fof(f131,plain,(
% 1.48/0.56    k10_relat_1(sK3,sK4) = k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) | ~v1_relat_1(sK3)),
% 1.48/0.56    inference(subsumption_resolution,[],[f126,f53])).
% 1.48/0.56  fof(f53,plain,(
% 1.48/0.56    v1_funct_1(sK3)),
% 1.48/0.56    inference(cnf_transformation,[],[f43])).
% 1.48/0.56  fof(f126,plain,(
% 1.48/0.56    k10_relat_1(sK3,sK4) = k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 1.48/0.56    inference(resolution,[],[f123,f63])).
% 1.48/0.56  fof(f63,plain,(
% 1.48/0.56    ( ! [X2,X0,X1] : (k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) | ~r1_tarski(k10_relat_1(X0,X2),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f25])).
% 1.48/0.56  fof(f25,plain,(
% 1.48/0.56    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) | ~r1_tarski(k10_relat_1(X0,X2),X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.48/0.56    inference(flattening,[],[f24])).
% 1.48/0.56  fof(f24,plain,(
% 1.48/0.56    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) | ~r1_tarski(k10_relat_1(X0,X2),X1)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.48/0.56    inference(ennf_transformation,[],[f13])).
% 1.48/0.56  fof(f13,axiom,(
% 1.48/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).
% 1.48/0.56  fof(f123,plain,(
% 1.48/0.56    r1_tarski(k10_relat_1(sK3,sK4),u1_struct_0(sK2))),
% 1.48/0.56    inference(backward_demodulation,[],[f57,f117])).
% 1.48/0.56  fof(f117,plain,(
% 1.48/0.56    ( ! [X2] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X2) = k10_relat_1(sK3,X2)) )),
% 1.48/0.56    inference(resolution,[],[f55,f74])).
% 1.48/0.56  fof(f74,plain,(
% 1.48/0.56    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.48/0.56    inference(cnf_transformation,[],[f35])).
% 1.48/0.56  fof(f35,plain,(
% 1.48/0.56    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.56    inference(ennf_transformation,[],[f10])).
% 1.48/0.56  fof(f10,axiom,(
% 1.48/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 1.48/0.56  fof(f57,plain,(
% 1.48/0.56    r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2))),
% 1.48/0.56    inference(cnf_transformation,[],[f43])).
% 1.48/0.56  fof(f189,plain,(
% 1.48/0.56    k10_relat_1(sK3,sK4) != k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) | ~m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 1.48/0.56    inference(forward_demodulation,[],[f187,f186])).
% 1.48/0.56  fof(f186,plain,(
% 1.48/0.56    k2_tmap_1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2))),
% 1.48/0.56    inference(resolution,[],[f122,f52])).
% 1.48/0.56  fof(f52,plain,(
% 1.48/0.56    m1_pre_topc(sK2,sK0)),
% 1.48/0.56    inference(cnf_transformation,[],[f43])).
% 1.48/0.56  fof(f122,plain,(
% 1.48/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))) )),
% 1.48/0.56    inference(backward_demodulation,[],[f114,f121])).
% 1.48/0.56  fof(f121,plain,(
% 1.48/0.56    ( ! [X1] : (k7_relat_1(sK3,X1) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X1)) )),
% 1.48/0.56    inference(subsumption_resolution,[],[f116,f53])).
% 1.48/0.56  fof(f116,plain,(
% 1.48/0.56    ( ! [X1] : (k7_relat_1(sK3,X1) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X1) | ~v1_funct_1(sK3)) )),
% 1.48/0.56    inference(resolution,[],[f55,f75])).
% 1.48/0.56  fof(f75,plain,(
% 1.48/0.56    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f37])).
% 1.48/0.56  fof(f37,plain,(
% 1.48/0.56    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.48/0.56    inference(flattening,[],[f36])).
% 1.48/0.56  fof(f36,plain,(
% 1.48/0.56    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.48/0.56    inference(ennf_transformation,[],[f12])).
% 1.48/0.56  fof(f12,axiom,(
% 1.48/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.48/0.56  fof(f114,plain,(
% 1.48/0.56    ( ! [X0] : (k2_tmap_1(sK0,sK1,sK3,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK0)) )),
% 1.48/0.56    inference(subsumption_resolution,[],[f113,f45])).
% 1.48/0.56  fof(f45,plain,(
% 1.48/0.56    ~v2_struct_0(sK0)),
% 1.48/0.56    inference(cnf_transformation,[],[f43])).
% 1.48/0.56  fof(f113,plain,(
% 1.48/0.56    ( ! [X0] : (k2_tmap_1(sK0,sK1,sK3,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0)) )),
% 1.48/0.56    inference(subsumption_resolution,[],[f112,f46])).
% 1.48/0.56  fof(f46,plain,(
% 1.48/0.56    v2_pre_topc(sK0)),
% 1.48/0.56    inference(cnf_transformation,[],[f43])).
% 1.48/0.56  fof(f112,plain,(
% 1.48/0.56    ( ! [X0] : (k2_tmap_1(sK0,sK1,sK3,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.48/0.56    inference(subsumption_resolution,[],[f111,f47])).
% 1.48/0.56  fof(f47,plain,(
% 1.48/0.56    l1_pre_topc(sK0)),
% 1.48/0.56    inference(cnf_transformation,[],[f43])).
% 1.48/0.56  fof(f111,plain,(
% 1.48/0.56    ( ! [X0] : (k2_tmap_1(sK0,sK1,sK3,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.48/0.56    inference(subsumption_resolution,[],[f110,f48])).
% 1.48/0.56  fof(f48,plain,(
% 1.48/0.56    ~v2_struct_0(sK1)),
% 1.48/0.56    inference(cnf_transformation,[],[f43])).
% 1.48/0.56  fof(f110,plain,(
% 1.48/0.56    ( ! [X0] : (k2_tmap_1(sK0,sK1,sK3,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.48/0.56    inference(subsumption_resolution,[],[f109,f49])).
% 1.48/0.56  fof(f49,plain,(
% 1.48/0.56    v2_pre_topc(sK1)),
% 1.48/0.56    inference(cnf_transformation,[],[f43])).
% 1.48/0.56  fof(f109,plain,(
% 1.48/0.56    ( ! [X0] : (k2_tmap_1(sK0,sK1,sK3,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.48/0.56    inference(subsumption_resolution,[],[f108,f50])).
% 1.48/0.56  fof(f50,plain,(
% 1.48/0.56    l1_pre_topc(sK1)),
% 1.48/0.56    inference(cnf_transformation,[],[f43])).
% 1.48/0.56  fof(f108,plain,(
% 1.48/0.56    ( ! [X0] : (k2_tmap_1(sK0,sK1,sK3,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.48/0.56    inference(subsumption_resolution,[],[f107,f53])).
% 1.48/0.56  fof(f107,plain,(
% 1.48/0.56    ( ! [X0] : (k2_tmap_1(sK0,sK1,sK3,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK0) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.48/0.56    inference(subsumption_resolution,[],[f106,f55])).
% 1.48/0.56  fof(f106,plain,(
% 1.48/0.56    ( ! [X0] : (k2_tmap_1(sK0,sK1,sK3,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.48/0.56    inference(resolution,[],[f54,f62])).
% 1.48/0.56  fof(f62,plain,(
% 1.48/0.56    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f23])).
% 1.48/0.56  fof(f23,plain,(
% 1.48/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.48/0.56    inference(flattening,[],[f22])).
% 1.48/0.56  fof(f22,plain,(
% 1.48/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.48/0.56    inference(ennf_transformation,[],[f14])).
% 1.48/0.56  fof(f14,axiom,(
% 1.48/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 1.48/0.56  fof(f54,plain,(
% 1.48/0.56    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.48/0.56    inference(cnf_transformation,[],[f43])).
% 1.48/0.56  fof(f187,plain,(
% 1.48/0.56    ~m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | k10_relat_1(sK3,sK4) != k10_relat_1(k2_tmap_1(sK0,sK1,sK3,sK2),sK4)),
% 1.48/0.56    inference(backward_demodulation,[],[f146,f186])).
% 1.48/0.56  fof(f146,plain,(
% 1.48/0.56    k10_relat_1(sK3,sK4) != k10_relat_1(k2_tmap_1(sK0,sK1,sK3,sK2),sK4) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 1.48/0.56    inference(superposition,[],[f124,f74])).
% 1.48/0.56  fof(f124,plain,(
% 1.48/0.56    k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) != k10_relat_1(sK3,sK4)),
% 1.48/0.56    inference(backward_demodulation,[],[f58,f117])).
% 1.48/0.56  fof(f58,plain,(
% 1.48/0.56    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4)),
% 1.48/0.56    inference(cnf_transformation,[],[f43])).
% 1.48/0.56  fof(f337,plain,(
% 1.48/0.56    ( ! [X5] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X5)),u1_struct_0(sK1))) )),
% 1.48/0.56    inference(resolution,[],[f182,f174])).
% 1.48/0.56  fof(f174,plain,(
% 1.48/0.56    ( ! [X5] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X5)),k2_relat_1(sK3))) )),
% 1.48/0.56    inference(subsumption_resolution,[],[f173,f139])).
% 1.48/0.56  fof(f173,plain,(
% 1.48/0.56    ( ! [X5] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X5)),k2_relat_1(sK3)) | ~v1_relat_1(k7_relat_1(sK3,X5))) )),
% 1.48/0.56    inference(subsumption_resolution,[],[f170,f125])).
% 1.48/0.56  fof(f170,plain,(
% 1.48/0.56    ( ! [X5] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X5)),k2_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(k7_relat_1(sK3,X5))) )),
% 1.48/0.56    inference(resolution,[],[f140,f60])).
% 1.48/0.56  fof(f60,plain,(
% 1.48/0.56    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f20])).
% 1.48/0.56  fof(f20,plain,(
% 1.48/0.56    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.48/0.56    inference(flattening,[],[f19])).
% 1.48/0.56  fof(f19,plain,(
% 1.48/0.56    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.48/0.56    inference(ennf_transformation,[],[f6])).
% 1.48/0.56  fof(f6,axiom,(
% 1.48/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 1.48/0.56  fof(f140,plain,(
% 1.48/0.56    ( ! [X8] : (r1_tarski(k7_relat_1(sK3,X8),sK3)) )),
% 1.48/0.56    inference(resolution,[],[f125,f66])).
% 1.48/0.56  fof(f66,plain,(
% 1.48/0.56    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f27])).
% 1.48/0.56  fof(f27,plain,(
% 1.48/0.56    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 1.48/0.56    inference(ennf_transformation,[],[f8])).
% 1.48/0.56  fof(f8,axiom,(
% 1.48/0.56    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 1.48/0.56  fof(f182,plain,(
% 1.48/0.56    ( ! [X2] : (~r1_tarski(X2,k2_relat_1(sK3)) | r1_tarski(X2,u1_struct_0(sK1))) )),
% 1.48/0.56    inference(resolution,[],[f148,f73])).
% 1.48/0.56  fof(f73,plain,(
% 1.48/0.56    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f34])).
% 1.48/0.56  fof(f34,plain,(
% 1.48/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.48/0.56    inference(flattening,[],[f33])).
% 1.48/0.56  fof(f33,plain,(
% 1.48/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.48/0.56    inference(ennf_transformation,[],[f1])).
% 1.48/0.56  fof(f1,axiom,(
% 1.48/0.56    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.48/0.56  fof(f148,plain,(
% 1.48/0.56    r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1))),
% 1.48/0.56    inference(subsumption_resolution,[],[f147,f125])).
% 1.48/0.56  fof(f147,plain,(
% 1.48/0.56    r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) | ~v1_relat_1(sK3)),
% 1.48/0.56    inference(resolution,[],[f119,f68])).
% 1.48/0.56  fof(f68,plain,(
% 1.48/0.56    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f44])).
% 1.48/0.56  fof(f44,plain,(
% 1.48/0.56    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.48/0.56    inference(nnf_transformation,[],[f29])).
% 1.48/0.56  fof(f29,plain,(
% 1.48/0.56    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.48/0.56    inference(ennf_transformation,[],[f3])).
% 1.48/0.56  fof(f3,axiom,(
% 1.48/0.56    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.48/0.56  fof(f119,plain,(
% 1.48/0.56    v5_relat_1(sK3,u1_struct_0(sK1))),
% 1.48/0.56    inference(resolution,[],[f55,f72])).
% 1.48/0.56  fof(f72,plain,(
% 1.48/0.56    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.48/0.56    inference(cnf_transformation,[],[f32])).
% 1.48/0.56  fof(f32,plain,(
% 1.48/0.56    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.56    inference(ennf_transformation,[],[f9])).
% 1.48/0.56  fof(f9,axiom,(
% 1.48/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.48/0.56  % SZS output end Proof for theBenchmark
% 1.48/0.56  % (15686)------------------------------
% 1.48/0.56  % (15686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (15686)Termination reason: Refutation
% 1.48/0.56  
% 1.48/0.56  % (15686)Memory used [KB]: 2046
% 1.48/0.56  % (15686)Time elapsed: 0.146 s
% 1.48/0.56  % (15686)------------------------------
% 1.48/0.56  % (15686)------------------------------
% 1.48/0.56  % (15694)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 1.48/0.56  % (15695)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 1.48/0.57  % (15681)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 1.48/0.57  % (15675)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 1.48/0.57  % (15680)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 1.48/0.58  % (15674)Success in time 0.216 s
%------------------------------------------------------------------------------
