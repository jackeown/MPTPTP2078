%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : pre_topc__t30_pre_topc.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:29 EDT 2019

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 384 expanded)
%              Number of leaves         :   20 ( 159 expanded)
%              Depth                    :   13
%              Number of atoms          :  351 (3227 expanded)
%              Number of equality atoms :   32 (  65 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f499,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f156,f239,f361,f382,f386,f465,f498])).

fof(f498,plain,
    ( spl9_5
    | ~ spl9_18 ),
    inference(avatar_contradiction_clause,[],[f497])).

fof(f497,plain,
    ( $false
    | ~ spl9_5
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f496,f467])).

fof(f467,plain,
    ( ~ m1_subset_1(k7_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,u1_struct_0(sK1))))
    | ~ spl9_5 ),
    inference(forward_demodulation,[],[f466,f218])).

fof(f218,plain,(
    ! [X4] : k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4) = k7_relat_1(sK2,X4) ),
    inference(resolution,[],[f92,f120])).

fof(f120,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t30_pre_topc.p',redefinition_k5_relset_1)).

fof(f92,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,
    ( ( ~ m1_subset_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK3)),u1_struct_0(sK1))))
      | ~ v1_funct_2(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),u1_struct_0(k1_pre_topc(sK0,sK3)),u1_struct_0(sK1))
      | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f40,f77,f76,f75,f74])).

fof(f74,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_subset_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X3)),u1_struct_0(X1))))
                    | ~ v1_funct_2(k5_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(sK0,X3)),u1_struct_0(X1))
                    | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3)) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))))
                    | ~ v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))
                    | ~ v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ~ m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(sK1))))
                  | ~ v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(sK1))
                  | ~ v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2,X3)) )
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ~ m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))))
                | ~ v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))
                | ~ v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( ( ~ m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))))
              | ~ v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))
              | ~ v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,X3)) )
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))))
            | ~ v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))
            | ~ v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,sK3)),u1_struct_0(X1))))
          | ~ v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3),u1_struct_0(k1_pre_topc(X0,sK3)),u1_struct_0(X1))
          | ~ v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3)) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))))
                    | ~ v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))
                    | ~ v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))))
                    | ~ v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))
                    | ~ v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))))
                      & v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))
                      & v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))))
                    & v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))
                    & v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t30_pre_topc.p',t30_pre_topc)).

fof(f466,plain,
    ( ~ m1_subset_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,u1_struct_0(sK1))))
    | ~ spl9_5 ),
    inference(forward_demodulation,[],[f155,f168])).

fof(f168,plain,(
    u1_struct_0(k1_pre_topc(sK0,sK3)) = sK3 ),
    inference(subsumption_resolution,[],[f161,f87])).

fof(f87,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f78])).

fof(f161,plain,
    ( u1_struct_0(k1_pre_topc(sK0,sK3)) = sK3
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f93,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t30_pre_topc.p',t29_pre_topc)).

fof(f93,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f78])).

fof(f155,plain,
    ( ~ m1_subset_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK3)),u1_struct_0(sK1))))
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl9_5
  <=> ~ m1_subset_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK3)),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f496,plain,
    ( m1_subset_1(k7_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,u1_struct_0(sK1))))
    | ~ spl9_18 ),
    inference(resolution,[],[f471,f163])).

fof(f163,plain,(
    r1_tarski(sK3,u1_struct_0(sK0)) ),
    inference(resolution,[],[f93,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t30_pre_topc.p',t3_subset)).

fof(f471,plain,
    ( ! [X3] :
        ( ~ r1_tarski(X3,u1_struct_0(sK0))
        | m1_subset_1(k7_relat_1(sK2,X3),k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK1)))) )
    | ~ spl9_18 ),
    inference(forward_demodulation,[],[f232,f224])).

fof(f224,plain,(
    ! [X1] : k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1) = k7_relat_1(sK2,X1) ),
    inference(subsumption_resolution,[],[f215,f90])).

fof(f90,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f78])).

fof(f215,plain,(
    ! [X1] :
      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1) = k7_relat_1(sK2,X1)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f92,f128])).

fof(f128,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t30_pre_topc.p',redefinition_k2_partfun1)).

fof(f232,plain,
    ( ! [X3] :
        ( ~ r1_tarski(X3,u1_struct_0(sK0))
        | m1_subset_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3),k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK1)))) )
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl9_18
  <=> ! [X3] :
        ( ~ r1_tarski(X3,u1_struct_0(sK0))
        | m1_subset_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3),k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK1)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f465,plain,
    ( spl9_3
    | ~ spl9_46 ),
    inference(avatar_contradiction_clause,[],[f464])).

fof(f464,plain,
    ( $false
    | ~ spl9_3
    | ~ spl9_46 ),
    inference(subsumption_resolution,[],[f463,f163])).

fof(f463,plain,
    ( ~ r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl9_3
    | ~ spl9_46 ),
    inference(resolution,[],[f360,f414])).

fof(f414,plain,
    ( ~ v1_funct_2(k7_relat_1(sK2,sK3),sK3,u1_struct_0(sK1))
    | ~ spl9_3 ),
    inference(backward_demodulation,[],[f218,f387])).

fof(f387,plain,
    ( ~ v1_funct_2(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK3,u1_struct_0(sK1))
    | ~ spl9_3 ),
    inference(forward_demodulation,[],[f149,f168])).

fof(f149,plain,
    ( ~ v1_funct_2(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),u1_struct_0(k1_pre_topc(sK0,sK3)),u1_struct_0(sK1))
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl9_3
  <=> ~ v1_funct_2(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),u1_struct_0(k1_pre_topc(sK0,sK3)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f360,plain,
    ( ! [X1] :
        ( v1_funct_2(k7_relat_1(sK2,X1),X1,u1_struct_0(sK1))
        | ~ r1_tarski(X1,u1_struct_0(sK0)) )
    | ~ spl9_46 ),
    inference(avatar_component_clause,[],[f359])).

fof(f359,plain,
    ( spl9_46
  <=> ! [X1] :
        ( v1_funct_2(k7_relat_1(sK2,X1),X1,u1_struct_0(sK1))
        | ~ r1_tarski(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).

fof(f386,plain,(
    spl9_1 ),
    inference(avatar_contradiction_clause,[],[f385])).

fof(f385,plain,
    ( $false
    | ~ spl9_1 ),
    inference(resolution,[],[f350,f345])).

fof(f345,plain,
    ( ~ v1_funct_1(k7_relat_1(sK2,sK3))
    | ~ spl9_1 ),
    inference(backward_demodulation,[],[f218,f143])).

fof(f143,plain,
    ( ~ v1_funct_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3))
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl9_1
  <=> ~ v1_funct_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f350,plain,(
    ! [X0] : v1_funct_1(k7_relat_1(sK2,X0)) ),
    inference(backward_demodulation,[],[f224,f223])).

fof(f223,plain,(
    ! [X0] : v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) ),
    inference(subsumption_resolution,[],[f214,f90])).

fof(f214,plain,(
    ! [X0] :
      ( v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0))
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f92,f129])).

fof(f129,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t30_pre_topc.p',dt_k2_partfun1)).

fof(f382,plain,(
    ~ spl9_20 ),
    inference(avatar_contradiction_clause,[],[f381])).

fof(f381,plain,
    ( $false
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f380,f88])).

fof(f88,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f78])).

fof(f380,plain,
    ( v2_struct_0(sK1)
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f379,f158])).

fof(f158,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f89,f97])).

fof(f97,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t30_pre_topc.p',dt_l1_pre_topc)).

fof(f89,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f78])).

fof(f379,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f374,f95])).

fof(f95,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t30_pre_topc.p',fc1_xboole_0)).

fof(f374,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl9_20 ),
    inference(superposition,[],[f103,f238])).

fof(f238,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f237])).

fof(f237,plain,
    ( spl9_20
  <=> u1_struct_0(sK1) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f103,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t30_pre_topc.p',fc2_struct_0)).

fof(f361,plain,
    ( spl9_20
    | spl9_46 ),
    inference(avatar_split_clause,[],[f357,f359,f237])).

fof(f357,plain,(
    ! [X1] :
      ( v1_funct_2(k7_relat_1(sK2,X1),X1,u1_struct_0(sK1))
      | u1_struct_0(sK1) = k1_xboole_0
      | ~ r1_tarski(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f356,f90])).

fof(f356,plain,(
    ! [X1] :
      ( v1_funct_2(k7_relat_1(sK2,X1),X1,u1_struct_0(sK1))
      | u1_struct_0(sK1) = k1_xboole_0
      | ~ r1_tarski(X1,u1_struct_0(sK0))
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f355,f91])).

fof(f91,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f78])).

fof(f355,plain,(
    ! [X1] :
      ( v1_funct_2(k7_relat_1(sK2,X1),X1,u1_struct_0(sK1))
      | u1_struct_0(sK1) = k1_xboole_0
      | ~ r1_tarski(X1,u1_struct_0(sK0))
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f352,f92])).

fof(f352,plain,(
    ! [X1] :
      ( v1_funct_2(k7_relat_1(sK2,X1),X1,u1_struct_0(sK1))
      | u1_struct_0(sK1) = k1_xboole_0
      | ~ r1_tarski(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK2) ) ),
    inference(superposition,[],[f124,f224])).

fof(f124,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t30_pre_topc.p',t38_funct_2)).

fof(f239,plain,
    ( spl9_18
    | spl9_20 ),
    inference(avatar_split_clause,[],[f229,f237,f231])).

fof(f229,plain,(
    ! [X3] :
      ( u1_struct_0(sK1) = k1_xboole_0
      | ~ r1_tarski(X3,u1_struct_0(sK0))
      | m1_subset_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3),k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK1)))) ) ),
    inference(subsumption_resolution,[],[f228,f90])).

fof(f228,plain,(
    ! [X3] :
      ( u1_struct_0(sK1) = k1_xboole_0
      | ~ r1_tarski(X3,u1_struct_0(sK0))
      | m1_subset_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3),k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK1))))
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f217,f91])).

fof(f217,plain,(
    ! [X3] :
      ( u1_struct_0(sK1) = k1_xboole_0
      | ~ r1_tarski(X3,u1_struct_0(sK0))
      | m1_subset_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3),k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK1))))
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f92,f126])).

fof(f126,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X2,X0)
      | m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f156,plain,
    ( ~ spl9_1
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f94,f154,f148,f142])).

fof(f94,plain,
    ( ~ m1_subset_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK3)),u1_struct_0(sK1))))
    | ~ v1_funct_2(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),u1_struct_0(k1_pre_topc(sK0,sK3)),u1_struct_0(sK1))
    | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)) ),
    inference(cnf_transformation,[],[f78])).
%------------------------------------------------------------------------------
