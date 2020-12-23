%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_2__t56_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:41 EDT 2019

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 953 expanded)
%              Number of leaves         :   28 ( 327 expanded)
%              Depth                    :   24
%              Number of atoms          :  786 (9580 expanded)
%              Number of equality atoms :   37 ( 107 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1459,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f138,f145,f149,f259,f270,f278,f482,f662,f700,f1458])).

fof(f1458,plain,
    ( spl8_3
    | ~ spl8_4
    | ~ spl8_32
    | ~ spl8_82
    | ~ spl8_84 ),
    inference(avatar_contradiction_clause,[],[f1457])).

fof(f1457,plain,
    ( $false
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_32
    | ~ spl8_82
    | ~ spl8_84 ),
    inference(subsumption_resolution,[],[f1456,f154])).

fof(f154,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f89,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t56_tops_2.p',cc1_relset_1)).

fof(f89,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,
    ( ( ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK3)))
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) )
      | ~ v5_pre_topc(sK2,sK0,sK1) )
    & ( ! [X4] :
          ( r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X4)))
          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
      | v5_pre_topc(sK2,sK0,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f66,f70,f69,f68,f67])).

fof(f67,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) )
                & ( ! [X4] :
                      ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | v5_pre_topc(X2,X0,X1) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ v5_pre_topc(X2,sK0,X1) )
              & ( ! [X4] :
                    ( r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)))
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                | v5_pre_topc(X2,sK0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ v5_pre_topc(X2,X0,X1) )
              & ( ! [X4] :
                    ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)))
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                | v5_pre_topc(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
     => ( ? [X2] :
            ( ( ? [X3] :
                  ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2,k2_pre_topc(sK1,X3)))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
              | ~ v5_pre_topc(X2,X0,sK1) )
            & ( ! [X4] :
                  ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2,k2_pre_topc(sK1,X4)))
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
              | v5_pre_topc(X2,X0,sK1) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ v5_pre_topc(X2,X0,X1) )
          & ( ! [X4] :
                ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)))
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
            | v5_pre_topc(X2,X0,X1) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ( ? [X3] :
              ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,k2_pre_topc(X1,X3)))
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ v5_pre_topc(sK2,X0,X1) )
        & ( ! [X4] :
              ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,k2_pre_topc(X1,X4)))
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
          | v5_pre_topc(sK2,X0,X1) )
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK3)))
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ v5_pre_topc(X2,X0,X1) )
              & ( ! [X4] :
                    ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)))
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                | v5_pre_topc(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(rectify,[],[f65])).

fof(f65,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ v5_pre_topc(X2,X0,X1) )
              & ( ! [X3] :
                    ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                | v5_pre_topc(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ v5_pre_topc(X2,X0,X1) )
              & ( ! [X3] :
                    ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                | v5_pre_topc(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <~> ! [X3] :
                    ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <~> ! [X3] :
                    ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
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
               => ( v5_pre_topc(X2,X0,X1)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t56_tops_2.p',t56_tops_2)).

fof(f1456,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_32
    | ~ spl8_82
    | ~ spl8_84 ),
    inference(subsumption_resolution,[],[f1454,f301])).

fof(f301,plain,
    ( r1_tarski(sK3,k2_pre_topc(sK1,sK3))
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f281,f86])).

fof(f86,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f71])).

fof(f281,plain,
    ( r1_tarski(sK3,k2_pre_topc(sK1,sK3))
    | ~ l1_pre_topc(sK1)
    | ~ spl8_4 ),
    inference(resolution,[],[f144,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t56_tops_2.p',t48_pre_topc)).

fof(f144,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl8_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f1454,plain,
    ( ~ r1_tarski(sK3,k2_pre_topc(sK1,sK3))
    | ~ v1_relat_1(sK2)
    | ~ spl8_3
    | ~ spl8_32
    | ~ spl8_82
    | ~ spl8_84 ),
    inference(resolution,[],[f1452,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t56_tops_2.p',t178_relat_1)).

fof(f1452,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK3),k10_relat_1(sK2,k2_pre_topc(sK1,sK3)))
    | ~ spl8_3
    | ~ spl8_32
    | ~ spl8_82
    | ~ spl8_84 ),
    inference(subsumption_resolution,[],[f1445,f357])).

fof(f357,plain,(
    ! [X0] : m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f348,f89])).

fof(f348,plain,(
    ! [X0] :
      ( m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ) ),
    inference(superposition,[],[f119,f153])).

fof(f153,plain,(
    ! [X1] : k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1) = k10_relat_1(sK2,X1) ),
    inference(resolution,[],[f89,f120])).

fof(f120,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t56_tops_2.p',redefinition_k8_relset_1)).

fof(f119,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t56_tops_2.p',dt_k8_relset_1)).

fof(f1445,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK3),k10_relat_1(sK2,k2_pre_topc(sK1,sK3)))
    | ~ m1_subset_1(k10_relat_1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_3
    | ~ spl8_32
    | ~ spl8_82
    | ~ spl8_84 ),
    inference(resolution,[],[f856,f350])).

fof(f350,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,sK3)),k10_relat_1(sK2,k2_pre_topc(sK1,sK3)))
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f346,f153])).

fof(f346,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)),k10_relat_1(sK2,k2_pre_topc(sK1,sK3)))
    | ~ spl8_3 ),
    inference(backward_demodulation,[],[f153,f137])).

fof(f137,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK3)))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl8_3
  <=> ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f856,plain,
    ( ! [X0] :
        ( r1_tarski(k2_pre_topc(sK0,X0),k10_relat_1(sK2,k2_pre_topc(sK1,sK3)))
        | ~ r1_tarski(X0,k10_relat_1(sK2,k2_pre_topc(sK1,sK3)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl8_32
    | ~ spl8_82
    | ~ spl8_84 ),
    inference(subsumption_resolution,[],[f855,f84])).

fof(f84,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f71])).

fof(f855,plain,
    ( ! [X0] :
        ( r1_tarski(k2_pre_topc(sK0,X0),k10_relat_1(sK2,k2_pre_topc(sK1,sK3)))
        | ~ r1_tarski(X0,k10_relat_1(sK2,k2_pre_topc(sK1,sK3)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl8_32
    | ~ spl8_82
    | ~ spl8_84 ),
    inference(subsumption_resolution,[],[f838,f357])).

fof(f838,plain,
    ( ! [X0] :
        ( r1_tarski(k2_pre_topc(sK0,X0),k10_relat_1(sK2,k2_pre_topc(sK1,sK3)))
        | ~ r1_tarski(X0,k10_relat_1(sK2,k2_pre_topc(sK1,sK3)))
        | ~ m1_subset_1(k10_relat_1(sK2,k2_pre_topc(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl8_32
    | ~ spl8_82
    | ~ spl8_84 ),
    inference(superposition,[],[f101,f754])).

fof(f754,plain,
    ( k2_pre_topc(sK0,k10_relat_1(sK2,k2_pre_topc(sK1,sK3))) = k10_relat_1(sK2,k2_pre_topc(sK1,sK3))
    | ~ spl8_32
    | ~ spl8_82
    | ~ spl8_84 ),
    inference(resolution,[],[f729,f366])).

fof(f366,plain,(
    ! [X1] :
      ( ~ v4_pre_topc(k10_relat_1(sK2,X1),sK0)
      | k2_pre_topc(sK0,k10_relat_1(sK2,X1)) = k10_relat_1(sK2,X1) ) ),
    inference(subsumption_resolution,[],[f359,f84])).

fof(f359,plain,(
    ! [X1] :
      ( ~ v4_pre_topc(k10_relat_1(sK2,X1),sK0)
      | k2_pre_topc(sK0,k10_relat_1(sK2,X1)) = k10_relat_1(sK2,X1)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f357,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t56_tops_2.p',t52_pre_topc)).

fof(f729,plain,
    ( v4_pre_topc(k10_relat_1(sK2,k2_pre_topc(sK1,sK3)),sK0)
    | ~ spl8_32
    | ~ spl8_82
    | ~ spl8_84 ),
    inference(subsumption_resolution,[],[f721,f636])).

fof(f636,plain,
    ( v4_pre_topc(k2_pre_topc(sK1,sK3),sK1)
    | ~ spl8_82 ),
    inference(avatar_component_clause,[],[f635])).

fof(f635,plain,
    ( spl8_82
  <=> v4_pre_topc(k2_pre_topc(sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_82])])).

fof(f721,plain,
    ( ~ v4_pre_topc(k2_pre_topc(sK1,sK3),sK1)
    | v4_pre_topc(k10_relat_1(sK2,k2_pre_topc(sK1,sK3)),sK0)
    | ~ spl8_32
    | ~ spl8_84 ),
    inference(resolution,[],[f658,f498])).

fof(f498,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v4_pre_topc(X0,sK1)
        | v4_pre_topc(k10_relat_1(sK2,X0),sK0) )
    | ~ spl8_32 ),
    inference(forward_demodulation,[],[f277,f153])).

fof(f277,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK1)
        | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f276])).

fof(f276,plain,
    ( spl8_32
  <=> ! [X0] :
        ( ~ v4_pre_topc(X0,sK1)
        | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f658,plain,
    ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl8_84 ),
    inference(avatar_component_clause,[],[f657])).

fof(f657,plain,
    ( spl8_84
  <=> m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_84])])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t56_tops_2.p',t49_pre_topc)).

fof(f700,plain,
    ( ~ spl8_4
    | spl8_85 ),
    inference(avatar_contradiction_clause,[],[f699])).

fof(f699,plain,
    ( $false
    | ~ spl8_4
    | ~ spl8_85 ),
    inference(subsumption_resolution,[],[f698,f86])).

fof(f698,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl8_4
    | ~ spl8_85 ),
    inference(subsumption_resolution,[],[f697,f144])).

fof(f697,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ spl8_85 ),
    inference(resolution,[],[f661,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t56_tops_2.p',dt_k2_pre_topc)).

fof(f661,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl8_85 ),
    inference(avatar_component_clause,[],[f660])).

fof(f660,plain,
    ( spl8_85
  <=> ~ m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_85])])).

fof(f662,plain,
    ( ~ spl8_85
    | spl8_82
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f629,f143,f635,f660])).

fof(f629,plain,
    ( v4_pre_topc(k2_pre_topc(sK1,sK3),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f628,f86])).

fof(f628,plain,
    ( v4_pre_topc(k2_pre_topc(sK1,sK3),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f607,f85])).

fof(f85,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f71])).

fof(f607,plain,
    ( v4_pre_topc(k2_pre_topc(sK1,sK3),sK1)
    | ~ v2_pre_topc(sK1)
    | ~ m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ spl8_4 ),
    inference(trivial_inequality_removal,[],[f606])).

fof(f606,plain,
    ( k2_pre_topc(sK1,sK3) != k2_pre_topc(sK1,sK3)
    | v4_pre_topc(k2_pre_topc(sK1,sK3),sK1)
    | ~ v2_pre_topc(sK1)
    | ~ m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ spl8_4 ),
    inference(superposition,[],[f100,f525])).

fof(f525,plain,
    ( k2_pre_topc(sK1,sK3) = k2_pre_topc(sK1,k2_pre_topc(sK1,sK3))
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f518,f86])).

fof(f518,plain,
    ( k2_pre_topc(sK1,sK3) = k2_pre_topc(sK1,k2_pre_topc(sK1,sK3))
    | ~ l1_pre_topc(sK1)
    | ~ spl8_4 ),
    inference(resolution,[],[f144,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t56_tops_2.p',projectivity_k2_pre_topc)).

fof(f100,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) != X1
      | v4_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f482,plain,
    ( spl8_1
    | ~ spl8_6
    | ~ spl8_28
    | ~ spl8_30 ),
    inference(avatar_contradiction_clause,[],[f481])).

fof(f481,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_6
    | ~ spl8_28
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f480,f84])).

fof(f480,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl8_1
    | ~ spl8_6
    | ~ spl8_28
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f479,f357])).

fof(f479,plain,
    ( ~ m1_subset_1(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl8_1
    | ~ spl8_6
    | ~ spl8_28
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f478,f83])).

fof(f83,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f71])).

fof(f478,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl8_1
    | ~ spl8_6
    | ~ spl8_28
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f452,f356])).

fof(f356,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f355,f84])).

fof(f355,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f354,f86])).

fof(f354,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f353,f87])).

fof(f87,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f71])).

fof(f353,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f352,f88])).

fof(f88,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f71])).

fof(f352,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f351,f89])).

fof(f351,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f347,f131])).

fof(f131,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl8_1
  <=> ~ v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f347,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f97,f153])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0)
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0)
                    & v4_pre_topc(sK4(X0,X1,X2),X1)
                    & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f73,f74])).

fof(f74,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0)
        & v4_pre_topc(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      | ~ v4_pre_topc(X3,X1)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( v4_pre_topc(X3,X1)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t56_tops_2.p',d12_pre_topc)).

fof(f452,plain,
    ( v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl8_6
    | ~ spl8_28
    | ~ spl8_30 ),
    inference(trivial_inequality_removal,[],[f451])).

fof(f451,plain,
    ( k10_relat_1(sK2,sK4(sK0,sK1,sK2)) != k10_relat_1(sK2,sK4(sK0,sK1,sK2))
    | v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl8_6
    | ~ spl8_28
    | ~ spl8_30 ),
    inference(superposition,[],[f100,f419])).

fof(f419,plain,
    ( k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2))) = k10_relat_1(sK2,sK4(sK0,sK1,sK2))
    | ~ spl8_6
    | ~ spl8_28
    | ~ spl8_30 ),
    inference(forward_demodulation,[],[f418,f323])).

fof(f323,plain,
    ( k2_pre_topc(sK1,sK4(sK0,sK1,sK2)) = sK4(sK0,sK1,sK2)
    | ~ spl8_28
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f322,f86])).

fof(f322,plain,
    ( k2_pre_topc(sK1,sK4(sK0,sK1,sK2)) = sK4(sK0,sK1,sK2)
    | ~ l1_pre_topc(sK1)
    | ~ spl8_28
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f315,f258])).

fof(f258,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f257])).

fof(f257,plain,
    ( spl8_28
  <=> v4_pre_topc(sK4(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f315,plain,
    ( ~ v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | k2_pre_topc(sK1,sK4(sK0,sK1,sK2)) = sK4(sK0,sK1,sK2)
    | ~ l1_pre_topc(sK1)
    | ~ spl8_30 ),
    inference(resolution,[],[f269,f99])).

fof(f269,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f268])).

fof(f268,plain,
    ( spl8_30
  <=> m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f418,plain,
    ( k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2))) = k10_relat_1(sK2,k2_pre_topc(sK1,sK4(sK0,sK1,sK2)))
    | ~ spl8_6
    | ~ spl8_28
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f417,f269])).

fof(f417,plain,
    ( k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2))) = k10_relat_1(sK2,k2_pre_topc(sK1,sK4(sK0,sK1,sK2)))
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl8_6
    | ~ spl8_28
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f409,f367])).

fof(f367,plain,(
    ! [X2] : r1_tarski(k10_relat_1(sK2,X2),k2_pre_topc(sK0,k10_relat_1(sK2,X2))) ),
    inference(subsumption_resolution,[],[f360,f84])).

fof(f360,plain,(
    ! [X2] :
      ( r1_tarski(k10_relat_1(sK2,X2),k2_pre_topc(sK0,k10_relat_1(sK2,X2)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f357,f98])).

fof(f409,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2))))
    | k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2))) = k10_relat_1(sK2,k2_pre_topc(sK1,sK4(sK0,sK1,sK2)))
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl8_6
    | ~ spl8_28
    | ~ spl8_30 ),
    inference(superposition,[],[f396,f323])).

fof(f396,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k10_relat_1(sK2,k2_pre_topc(sK1,X1)),k2_pre_topc(sK0,k10_relat_1(sK2,X1)))
        | k2_pre_topc(sK0,k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k2_pre_topc(sK1,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl8_6 ),
    inference(resolution,[],[f349,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t56_tops_2.p',d10_xboole_0)).

fof(f349,plain,
    ( ! [X4] :
        ( r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,X4)),k10_relat_1(sK2,k2_pre_topc(sK1,X4)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f345,f153])).

fof(f345,plain,
    ( ! [X4] :
        ( r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4)),k10_relat_1(sK2,k2_pre_topc(sK1,X4)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f153,f148])).

fof(f148,plain,
    ( ! [X4] :
        ( r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X4)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl8_6
  <=> ! [X4] :
        ( r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X4)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f278,plain,
    ( ~ spl8_1
    | spl8_32 ),
    inference(avatar_split_clause,[],[f274,f276,f130])).

fof(f274,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0) ) ),
    inference(subsumption_resolution,[],[f273,f84])).

fof(f273,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f272,f86])).

fof(f272,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
      | ~ l1_pre_topc(sK1)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f271,f87])).

fof(f271,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
      | ~ v1_funct_1(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f150,f88])).

fof(f150,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f89,f94])).

fof(f94,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f270,plain,
    ( spl8_0
    | spl8_30 ),
    inference(avatar_split_clause,[],[f263,f268,f127])).

fof(f127,plain,
    ( spl8_0
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f263,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f262,f84])).

fof(f262,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f261,f86])).

fof(f261,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f260,f87])).

fof(f260,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f151,f88])).

fof(f151,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f89,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f259,plain,
    ( spl8_0
    | spl8_28 ),
    inference(avatar_split_clause,[],[f252,f257,f127])).

fof(f252,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f251,f84])).

fof(f251,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f250,f86])).

fof(f250,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f249,f87])).

fof(f249,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f152,f88])).

fof(f152,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f89,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v4_pre_topc(sK4(X0,X1,X2),X1)
      | v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f149,plain,
    ( spl8_0
    | spl8_6 ),
    inference(avatar_split_clause,[],[f90,f147,f127])).

fof(f90,plain,(
    ! [X4] :
      ( r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X4)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))
      | v5_pre_topc(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f145,plain,
    ( ~ spl8_1
    | spl8_4 ),
    inference(avatar_split_clause,[],[f91,f143,f130])).

fof(f91,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f71])).

fof(f138,plain,
    ( ~ spl8_1
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f92,f136,f130])).

fof(f92,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK3)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f71])).
%------------------------------------------------------------------------------
