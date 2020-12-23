%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_2__t57_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:41 EDT 2019

% Result     : Theorem 115.26s
% Output     : Refutation 115.26s
% Verified   : 
% Statistics : Number of formulae       :  229 (1030 expanded)
%              Number of leaves         :   42 ( 352 expanded)
%              Depth                    :   22
%              Number of atoms          :  927 (10426 expanded)
%              Number of equality atoms :   49 ( 102 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f268608,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f180,f187,f191,f344,f454,f479,f616,f905,f1182,f1237,f16154,f20527,f222356,f268607])).

fof(f268607,plain,
    ( ~ spl8_0
    | ~ spl8_4
    | ~ spl8_40
    | ~ spl8_42
    | ~ spl8_58
    | ~ spl8_1032 ),
    inference(avatar_contradiction_clause,[],[f268606])).

fof(f268606,plain,
    ( $false
    | ~ spl8_0
    | ~ spl8_4
    | ~ spl8_40
    | ~ spl8_42
    | ~ spl8_58
    | ~ spl8_1032 ),
    inference(subsumption_resolution,[],[f239786,f20014])).

fof(f20014,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,k10_relat_1(sK2,k9_relat_1(sK2,X0)))),k2_pre_topc(sK1,k9_relat_1(sK2,X0)))
    | ~ spl8_0
    | ~ spl8_40
    | ~ spl8_42 ),
    inference(resolution,[],[f18099,f5762])).

fof(f5762,plain,
    ( ! [X6,X5] :
        ( ~ r1_tarski(X5,k10_relat_1(sK2,X6))
        | r1_tarski(k9_relat_1(sK2,X5),X6) )
    | ~ spl8_40
    | ~ spl8_42 ),
    inference(subsumption_resolution,[],[f5758,f316])).

fof(f316,plain,
    ( v1_relat_1(sK2)
    | ~ spl8_40 ),
    inference(avatar_component_clause,[],[f315])).

fof(f315,plain,
    ( spl8_40
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f5758,plain,
    ( ! [X6,X5] :
        ( r1_tarski(k9_relat_1(sK2,X5),X6)
        | ~ r1_tarski(X5,k10_relat_1(sK2,X6))
        | ~ v1_relat_1(sK2) )
    | ~ spl8_42 ),
    inference(resolution,[],[f744,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t57_tops_2.p',t156_relat_1)).

fof(f744,plain,
    ( ! [X10,X9] :
        ( ~ r1_tarski(X9,k9_relat_1(sK2,k10_relat_1(sK2,X10)))
        | r1_tarski(X9,X10) )
    | ~ spl8_42 ),
    inference(resolution,[],[f322,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t57_tops_2.p',t1_xboole_1)).

fof(f322,plain,
    ( ! [X7] : r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X7)),X7)
    | ~ spl8_42 ),
    inference(avatar_component_clause,[],[f321])).

fof(f321,plain,
    ( spl8_42
  <=> ! [X7] : r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X7)),X7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f18099,plain,
    ( ! [X11] : r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,k9_relat_1(sK2,X11))),k10_relat_1(sK2,k2_pre_topc(sK1,k9_relat_1(sK2,X11))))
    | ~ spl8_0 ),
    inference(resolution,[],[f16166,f1820])).

fof(f1820,plain,(
    ! [X2] : m1_subset_1(k9_relat_1(sK2,X2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f427,f426])).

fof(f426,plain,(
    ! [X1] : k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1) = k9_relat_1(sK2,X1) ),
    inference(resolution,[],[f117,f132])).

fof(f132,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t57_tops_2.p',redefinition_k7_relset_1)).

fof(f117,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f97])).

fof(f97,plain,
    ( ( ( ~ r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)))
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | ~ v5_pre_topc(sK2,sK0,sK1) )
    & ( ! [X4] :
          ( r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X4)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4)))
          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
      | v5_pre_topc(sK2,sK0,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f92,f96,f95,f94,f93])).

fof(f93,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v5_pre_topc(X2,X0,X1) )
                & ( ! [X4] :
                      ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | v5_pre_topc(X2,X0,X1) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_pre_topc(sK0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3)))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
                | ~ v5_pre_topc(X2,sK0,X1) )
              & ( ! [X4] :
                    ( r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_pre_topc(sK0,X4)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X4)))
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
                | v5_pre_topc(X2,sK0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f94,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ v5_pre_topc(X2,X0,X1) )
              & ( ! [X4] :
                    ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)))
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                | v5_pre_topc(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ( ? [X3] :
                  ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2,X3)))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v5_pre_topc(X2,X0,sK1) )
            & ( ! [X4] :
                  ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2,k2_pre_topc(X0,X4)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2,X4)))
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | v5_pre_topc(X2,X0,sK1) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v5_pre_topc(X2,X0,X1) )
          & ( ! [X4] :
                ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)))
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | v5_pre_topc(X2,X0,X1) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ( ? [X3] :
              ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,X3)))
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v5_pre_topc(sK2,X0,X1) )
        & ( ! [X4] :
              ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,k2_pre_topc(X0,X4)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,X4)))
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | v5_pre_topc(sK2,X0,X1) )
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3)))
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f92,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ v5_pre_topc(X2,X0,X1) )
              & ( ! [X4] :
                    ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)))
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                | v5_pre_topc(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(rectify,[],[f91])).

fof(f91,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ v5_pre_topc(X2,X0,X1) )
              & ( ! [X3] :
                    ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | v5_pre_topc(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f90])).

fof(f90,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ v5_pre_topc(X2,X0,X1) )
              & ( ! [X3] :
                    ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | v5_pre_topc(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <~> ! [X3] :
                    ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <~> ! [X3] :
                    ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( v5_pre_topc(X2,X0,X1)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t57_tops_2.p',t57_tops_2)).

fof(f427,plain,(
    ! [X2] : m1_subset_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(resolution,[],[f117,f133])).

fof(f133,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t57_tops_2.p',dt_k7_relset_1)).

fof(f16166,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,X0)),k10_relat_1(sK2,k2_pre_topc(sK1,X0))) )
    | ~ spl8_0 ),
    inference(forward_demodulation,[],[f16165,f429])).

fof(f429,plain,(
    ! [X3] : k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3) = k10_relat_1(sK2,X3) ),
    inference(resolution,[],[f117,f142])).

fof(f142,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t57_tops_2.p',redefinition_k8_relset_1)).

fof(f16165,plain,
    ( ! [X0] :
        ( r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)),k10_relat_1(sK2,k2_pre_topc(sK1,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl8_0 ),
    inference(forward_demodulation,[],[f16164,f429])).

fof(f16164,plain,
    ( ! [X0] :
        ( r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl8_0 ),
    inference(subsumption_resolution,[],[f16163,f110])).

fof(f110,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f97])).

fof(f16163,plain,
    ( ! [X0] :
        ( r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v2_pre_topc(sK0) )
    | ~ spl8_0 ),
    inference(subsumption_resolution,[],[f16162,f111])).

fof(f111,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f97])).

fof(f16162,plain,
    ( ! [X0] :
        ( r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl8_0 ),
    inference(subsumption_resolution,[],[f16161,f113])).

fof(f113,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f97])).

fof(f16161,plain,
    ( ! [X0] :
        ( r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl8_0 ),
    inference(subsumption_resolution,[],[f16160,f114])).

fof(f114,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f97])).

fof(f16160,plain,
    ( ! [X0] :
        ( r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl8_0 ),
    inference(subsumption_resolution,[],[f16159,f115])).

fof(f115,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f97])).

fof(f16159,plain,
    ( ! [X0] :
        ( r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v1_funct_1(sK2)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl8_0 ),
    inference(subsumption_resolution,[],[f16158,f116])).

fof(f116,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f97])).

fof(f16158,plain,
    ( ! [X0] :
        ( r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl8_0 ),
    inference(subsumption_resolution,[],[f16157,f117])).

fof(f16157,plain,
    ( ! [X0] :
        ( r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl8_0 ),
    inference(resolution,[],[f170,f128])).

fof(f128,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f102,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK4(X0,X1,X2))))
                    & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f100,f101])).

fof(f101,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK4(X0,X1,X2))))
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f100,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f99])).

fof(f99,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
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
    file('/export/starexec/sandbox/benchmark/tops_2__t57_tops_2.p',t56_tops_2)).

fof(f170,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ spl8_0 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl8_0
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f239786,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK3)))),k2_pre_topc(sK1,k9_relat_1(sK2,sK3)))
    | ~ spl8_4
    | ~ spl8_40
    | ~ spl8_58
    | ~ spl8_1032 ),
    inference(subsumption_resolution,[],[f239780,f4135])).

fof(f4135,plain,(
    ! [X4] : m1_subset_1(k10_relat_1(sK2,X4),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f3409,f429])).

fof(f3409,plain,(
    ! [X4] : m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f117,f143])).

fof(f143,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t57_tops_2.p',dt_k8_relset_1)).

fof(f239780,plain,
    ( ~ m1_subset_1(k10_relat_1(sK2,k9_relat_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK3)))),k2_pre_topc(sK1,k9_relat_1(sK2,sK3)))
    | ~ spl8_4
    | ~ spl8_40
    | ~ spl8_58
    | ~ spl8_1032 ),
    inference(resolution,[],[f20526,f16221])).

fof(f16221,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,k9_relat_1(sK2,sK3)))
    | ~ spl8_4
    | ~ spl8_40
    | ~ spl8_58 ),
    inference(resolution,[],[f16188,f6165])).

fof(f6165,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0))) )
    | ~ spl8_40
    | ~ spl8_58 ),
    inference(forward_demodulation,[],[f480,f948])).

fof(f948,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl8_58 ),
    inference(subsumption_resolution,[],[f943,f117])).

fof(f943,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl8_58 ),
    inference(superposition,[],[f418,f151])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t57_tops_2.p',redefinition_k1_relset_1)).

fof(f418,plain,
    ( u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl8_58 ),
    inference(avatar_component_clause,[],[f417])).

fof(f417,plain,
    ( spl8_58
  <=> u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_58])])).

fof(f480,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0)))
        | ~ r1_tarski(X0,k1_relat_1(sK2)) )
    | ~ spl8_40 ),
    inference(resolution,[],[f316,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t57_tops_2.p',t146_funct_1)).

fof(f16188,plain,
    ( r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl8_4 ),
    inference(resolution,[],[f186,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t57_tops_2.p',t3_subset)).

fof(f186,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl8_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f20526,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK3,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,X0)),k2_pre_topc(sK1,k9_relat_1(sK2,sK3))) )
    | ~ spl8_1032 ),
    inference(avatar_component_clause,[],[f20525])).

fof(f20525,plain,
    ( spl8_1032
  <=> ! [X0] :
        ( ~ r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,X0)),k2_pre_topc(sK1,k9_relat_1(sK2,sK3)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1032])])).

fof(f222356,plain,
    ( ~ spl8_6
    | ~ spl8_40
    | ~ spl8_42
    | ~ spl8_52
    | spl8_55
    | ~ spl8_58 ),
    inference(avatar_contradiction_clause,[],[f222355])).

fof(f222355,plain,
    ( $false
    | ~ spl8_6
    | ~ spl8_40
    | ~ spl8_42
    | ~ spl8_52
    | ~ spl8_55
    | ~ spl8_58 ),
    inference(subsumption_resolution,[],[f222354,f316])).

fof(f222354,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl8_6
    | ~ spl8_40
    | ~ spl8_42
    | ~ spl8_52
    | ~ spl8_55
    | ~ spl8_58 ),
    inference(subsumption_resolution,[],[f222351,f40704])).

fof(f40704,plain,
    ( r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2)))),k2_pre_topc(sK1,sK4(sK0,sK1,sK2)))
    | ~ spl8_6
    | ~ spl8_42
    | ~ spl8_52 ),
    inference(resolution,[],[f7510,f9007])).

fof(f9007,plain,
    ( r1_tarski(k2_pre_topc(sK1,k9_relat_1(sK2,k10_relat_1(sK2,sK4(sK0,sK1,sK2)))),k2_pre_topc(sK1,sK4(sK0,sK1,sK2)))
    | ~ spl8_42
    | ~ spl8_52 ),
    inference(subsumption_resolution,[],[f9006,f1820])).

fof(f9006,plain,
    ( r1_tarski(k2_pre_topc(sK1,k9_relat_1(sK2,k10_relat_1(sK2,sK4(sK0,sK1,sK2)))),k2_pre_topc(sK1,sK4(sK0,sK1,sK2)))
    | ~ m1_subset_1(k9_relat_1(sK2,k10_relat_1(sK2,sK4(sK0,sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl8_42
    | ~ spl8_52 ),
    inference(resolution,[],[f1405,f322])).

fof(f1405,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,sK4(sK0,sK1,sK2))
        | r1_tarski(k2_pre_topc(sK1,X1),k2_pre_topc(sK1,sK4(sK0,sK1,sK2)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl8_52 ),
    inference(subsumption_resolution,[],[f1396,f114])).

fof(f1396,plain,
    ( ! [X1] :
        ( r1_tarski(k2_pre_topc(sK1,X1),k2_pre_topc(sK1,sK4(sK0,sK1,sK2)))
        | ~ r1_tarski(X1,sK4(sK0,sK1,sK2))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_pre_topc(sK1) )
    | ~ spl8_52 ),
    inference(resolution,[],[f369,f131])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t57_tops_2.p',t49_pre_topc)).

fof(f369,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl8_52 ),
    inference(avatar_component_clause,[],[f368])).

fof(f368,plain,
    ( spl8_52
  <=> m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).

fof(f7510,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_pre_topc(sK1,k9_relat_1(sK2,k10_relat_1(sK2,X0))),X1)
        | r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,k10_relat_1(sK2,X0))),X1) )
    | ~ spl8_6 ),
    inference(resolution,[],[f4295,f121])).

fof(f4295,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,k10_relat_1(sK2,X0))),k2_pre_topc(sK1,k9_relat_1(sK2,k10_relat_1(sK2,X0))))
    | ~ spl8_6 ),
    inference(resolution,[],[f4135,f4146])).

fof(f4146,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,X4)),k2_pre_topc(sK1,k9_relat_1(sK2,X4))) )
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f4145,f426])).

fof(f4145,plain,
    ( ! [X4] :
        ( r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X4)),k2_pre_topc(sK1,k9_relat_1(sK2,X4)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f190,f426])).

fof(f190,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X4)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4))) )
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl8_6
  <=> ! [X4] :
        ( r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X4)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f222351,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2)))),k2_pre_topc(sK1,sK4(sK0,sK1,sK2)))
    | ~ v1_relat_1(sK2)
    | ~ spl8_40
    | ~ spl8_55
    | ~ spl8_58 ),
    inference(resolution,[],[f67367,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t57_tops_2.p',t178_relat_1)).

fof(f67367,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2))))),k10_relat_1(sK2,k2_pre_topc(sK1,sK4(sK0,sK1,sK2))))
    | ~ spl8_40
    | ~ spl8_55
    | ~ spl8_58 ),
    inference(subsumption_resolution,[],[f67366,f5555])).

fof(f5555,plain,(
    ! [X17] : r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,X17)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f4305,f124])).

fof(f4305,plain,(
    ! [X1] : m1_subset_1(k2_pre_topc(sK0,k10_relat_1(sK2,X1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f4296,f111])).

fof(f4296,plain,(
    ! [X1] :
      ( m1_subset_1(k2_pre_topc(sK0,k10_relat_1(sK2,X1)),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f4135,f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t57_tops_2.p',dt_k2_pre_topc)).

fof(f67366,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2))),u1_struct_0(sK0))
    | ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2))))),k10_relat_1(sK2,k2_pre_topc(sK1,sK4(sK0,sK1,sK2))))
    | ~ spl8_40
    | ~ spl8_55
    | ~ spl8_58 ),
    inference(forward_demodulation,[],[f67363,f948])).

fof(f67363,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2))),k1_relat_1(sK2))
    | ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2))))),k10_relat_1(sK2,k2_pre_topc(sK1,sK4(sK0,sK1,sK2))))
    | ~ spl8_40
    | ~ spl8_55 ),
    inference(resolution,[],[f8824,f316])).

fof(f8824,plain,
    ( ! [X4] :
        ( ~ v1_relat_1(X4)
        | ~ r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2))),k1_relat_1(X4))
        | ~ r1_tarski(k10_relat_1(X4,k9_relat_1(X4,k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2))))),k10_relat_1(sK2,k2_pre_topc(sK1,sK4(sK0,sK1,sK2)))) )
    | ~ spl8_55 ),
    inference(resolution,[],[f3034,f127])).

fof(f3034,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2))),X0)
        | ~ r1_tarski(X0,k10_relat_1(sK2,k2_pre_topc(sK1,sK4(sK0,sK1,sK2)))) )
    | ~ spl8_55 ),
    inference(resolution,[],[f2989,f121])).

fof(f2989,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK0,sK1,sK2))),k10_relat_1(sK2,k2_pre_topc(sK1,sK4(sK0,sK1,sK2))))
    | ~ spl8_55 ),
    inference(forward_demodulation,[],[f2988,f429])).

fof(f2988,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2))),k10_relat_1(sK2,k2_pre_topc(sK1,sK4(sK0,sK1,sK2))))
    | ~ spl8_55 ),
    inference(forward_demodulation,[],[f381,f429])).

fof(f381,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK4(sK0,sK1,sK2))))
    | ~ spl8_55 ),
    inference(avatar_component_clause,[],[f380])).

fof(f380,plain,
    ( spl8_55
  <=> ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK4(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_55])])).

fof(f20527,plain,
    ( ~ spl8_5
    | spl8_1032
    | spl8_3
    | ~ spl8_40 ),
    inference(avatar_split_clause,[],[f19951,f315,f178,f20525,f182])).

fof(f182,plain,
    ( spl8_5
  <=> ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f178,plain,
    ( spl8_3
  <=> ~ r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f19951,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,X0)),k2_pre_topc(sK1,k9_relat_1(sK2,sK3)))
        | ~ r1_tarski(sK3,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl8_3
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f19947,f111])).

fof(f19947,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,X0)),k2_pre_topc(sK1,k9_relat_1(sK2,sK3)))
        | ~ r1_tarski(sK3,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl8_3
    | ~ spl8_40 ),
    inference(resolution,[],[f18770,f131])).

fof(f18770,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_pre_topc(sK0,sK3),X0)
        | ~ r1_tarski(k9_relat_1(sK2,X0),k2_pre_topc(sK1,k9_relat_1(sK2,sK3))) )
    | ~ spl8_3
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f18766,f316])).

fof(f18766,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k9_relat_1(sK2,X0),k2_pre_topc(sK1,k9_relat_1(sK2,sK3)))
        | ~ r1_tarski(k2_pre_topc(sK0,sK3),X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl8_3 ),
    inference(resolution,[],[f16235,f123])).

fof(f16235,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,sK3)),X0)
        | ~ r1_tarski(X0,k2_pre_topc(sK1,k9_relat_1(sK2,sK3))) )
    | ~ spl8_3 ),
    inference(resolution,[],[f16156,f121])).

fof(f16156,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k2_pre_topc(sK0,sK3)),k2_pre_topc(sK1,k9_relat_1(sK2,sK3)))
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f16155,f426])).

fof(f16155,plain,
    ( ~ r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)),k2_pre_topc(sK1,k9_relat_1(sK2,sK3)))
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f179,f426])).

fof(f179,plain,
    ( ~ r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f178])).

fof(f16154,plain,
    ( spl8_52
    | spl8_0 ),
    inference(avatar_split_clause,[],[f16153,f169,f368])).

fof(f16153,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f16152,f110])).

fof(f16152,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f16151,f111])).

fof(f16151,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f16150,f113])).

fof(f16150,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f16149,f114])).

fof(f16149,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f16148,f115])).

fof(f16148,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f3403,f116])).

fof(f3403,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f117,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f1237,plain,
    ( ~ spl8_51
    | ~ spl8_55
    | spl8_1 ),
    inference(avatar_split_clause,[],[f1236,f172,f380,f362])).

fof(f362,plain,
    ( spl8_51
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).

fof(f172,plain,
    ( spl8_1
  <=> ~ v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f1236,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK4(sK0,sK1,sK2))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f1235,f110])).

fof(f1235,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK4(sK0,sK1,sK2))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f1234,f111])).

fof(f1234,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK4(sK0,sK1,sK2))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f1233,f113])).

fof(f1233,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK4(sK0,sK1,sK2))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f1232,f114])).

fof(f1232,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK4(sK0,sK1,sK2))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f1231,f115])).

fof(f1231,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK4(sK0,sK1,sK2))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f1222,f173])).

fof(f173,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f172])).

fof(f1222,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK4(sK0,sK1,sK2))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f116,f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK4(X0,X1,X2))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f1182,plain,
    ( ~ spl8_41
    | spl8_42 ),
    inference(avatar_split_clause,[],[f1181,f321,f318])).

fof(f318,plain,
    ( spl8_41
  <=> ~ v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).

fof(f1181,plain,(
    ! [X7] :
      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X7)),X7)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f115,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t57_tops_2.p',t145_funct_1)).

fof(f905,plain,(
    spl8_51 ),
    inference(avatar_contradiction_clause,[],[f904])).

fof(f904,plain,
    ( $false
    | ~ spl8_51 ),
    inference(subsumption_resolution,[],[f363,f117])).

fof(f363,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl8_51 ),
    inference(avatar_component_clause,[],[f362])).

fof(f616,plain,
    ( ~ spl8_22
    | ~ spl8_56 ),
    inference(avatar_contradiction_clause,[],[f615])).

fof(f615,plain,
    ( $false
    | ~ spl8_22
    | ~ spl8_56 ),
    inference(subsumption_resolution,[],[f614,f112])).

fof(f112,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f97])).

fof(f614,plain,
    ( v2_struct_0(sK1)
    | ~ spl8_22
    | ~ spl8_56 ),
    inference(subsumption_resolution,[],[f613,f247])).

fof(f247,plain,
    ( l1_struct_0(sK1)
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f246])).

fof(f246,plain,
    ( spl8_22
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f613,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl8_56 ),
    inference(subsumption_resolution,[],[f526,f160])).

fof(f160,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t57_tops_2.p',fc1_xboole_0)).

fof(f526,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl8_56 ),
    inference(superposition,[],[f152,f412])).

fof(f412,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | ~ spl8_56 ),
    inference(avatar_component_clause,[],[f411])).

fof(f411,plain,
    ( spl8_56
  <=> u1_struct_0(sK1) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_56])])).

fof(f152,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f45])).

fof(f45,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t57_tops_2.p',fc2_struct_0)).

fof(f479,plain,
    ( spl8_56
    | spl8_58 ),
    inference(avatar_split_clause,[],[f455,f417,f411])).

fof(f455,plain,
    ( u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | u1_struct_0(sK1) = k1_xboole_0 ),
    inference(subsumption_resolution,[],[f431,f116])).

fof(f431,plain,
    ( u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | u1_struct_0(sK1) = k1_xboole_0 ),
    inference(resolution,[],[f117,f144])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f105,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t57_tops_2.p',d1_funct_2)).

fof(f454,plain,(
    spl8_41 ),
    inference(avatar_contradiction_clause,[],[f453])).

fof(f453,plain,
    ( $false
    | ~ spl8_41 ),
    inference(subsumption_resolution,[],[f428,f319])).

fof(f319,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl8_41 ),
    inference(avatar_component_clause,[],[f318])).

fof(f428,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f117,f138])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t57_tops_2.p',cc1_relset_1)).

fof(f344,plain,(
    spl8_23 ),
    inference(avatar_contradiction_clause,[],[f343])).

fof(f343,plain,
    ( $false
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f342,f114])).

fof(f342,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl8_23 ),
    inference(resolution,[],[f250,f156])).

fof(f156,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t57_tops_2.p',dt_l1_pre_topc)).

fof(f250,plain,
    ( ~ l1_struct_0(sK1)
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f249])).

fof(f249,plain,
    ( spl8_23
  <=> ~ l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f191,plain,
    ( spl8_0
    | spl8_6 ),
    inference(avatar_split_clause,[],[f118,f189,f169])).

fof(f118,plain,(
    ! [X4] :
      ( r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X4)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | v5_pre_topc(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f187,plain,
    ( ~ spl8_1
    | spl8_4 ),
    inference(avatar_split_clause,[],[f119,f185,f172])).

fof(f119,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f97])).

fof(f180,plain,
    ( ~ spl8_1
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f120,f178,f172])).

fof(f120,plain,
    ( ~ r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f97])).
%------------------------------------------------------------------------------
