%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  165 (6897 expanded)
%              Number of leaves         :   21 (2487 expanded)
%              Depth                    :   24
%              Number of atoms          :  972 (81183 expanded)
%              Number of equality atoms :  143 (12966 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f783,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f732,f764,f780])).

fof(f780,plain,
    ( spl5_13
    | ~ spl5_14 ),
    inference(avatar_contradiction_clause,[],[f776])).

fof(f776,plain,
    ( $false
    | spl5_13
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f726,f774])).

fof(f774,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f773,f698])).

fof(f698,plain,(
    sK4(sK0,sK1,sK2) = k10_relat_1(sK2,k9_relat_1(sK2,sK4(sK0,sK1,sK2))) ),
    inference(unit_resulting_resolution,[],[f111,f64,f71,f696,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

fof(f696,plain,(
    r1_tarski(sK4(sK0,sK1,sK2),k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f690,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f690,plain,(
    m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(k1_relat_1(sK2))) ),
    inference(unit_resulting_resolution,[],[f64,f71,f73,f136,f137,f142,f138,f689])).

fof(f689,plain,(
    ! [X0] :
      ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X0)
      | m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(k1_relat_1(sK2)))
      | ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
      | k1_relat_1(sK2) != k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X0)
      | v3_tops_2(X0,sK0,sK1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0) ) ),
    inference(global_subsumption,[],[f63,f61,f688])).

fof(f688,plain,(
    ! [X0] :
      ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X0)
      | ~ v2_funct_1(X0)
      | v3_tops_2(X0,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2))
      | k1_relat_1(sK2) != k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X0)
      | m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(k1_relat_1(sK2)))
      | ~ v1_funct_1(X0) ) ),
    inference(forward_demodulation,[],[f685,f125])).

fof(f125,plain,(
    k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f109,f121])).

fof(f121,plain,(
    u1_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f110,f113])).

fof(f113,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f66,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f66,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ~ v3_tops_2(sK2,sK0,sK1)
    & v5_pre_topc(sK2,sK0,sK1)
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & v8_pre_topc(sK1)
    & v1_compts_1(sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f46,f45,f44])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v3_tops_2(X2,X0,X1)
                & v5_pre_topc(X2,X0,X1)
                & v2_funct_1(X2)
                & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                & v8_pre_topc(X1)
                & v1_compts_1(X0)
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
              ( ~ v3_tops_2(X2,sK0,X1)
              & v5_pre_topc(X2,sK0,X1)
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
              & k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
              & v8_pre_topc(X1)
              & v1_compts_1(sK0)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v3_tops_2(X2,sK0,X1)
            & v5_pre_topc(X2,sK0,X1)
            & v2_funct_1(X2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
            & k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
            & v8_pre_topc(X1)
            & v1_compts_1(sK0)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ v3_tops_2(X2,sK0,sK1)
          & v5_pre_topc(X2,sK0,sK1)
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
          & k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)
          & v8_pre_topc(sK1)
          & v1_compts_1(sK0)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X2] :
        ( ~ v3_tops_2(X2,sK0,sK1)
        & v5_pre_topc(X2,sK0,sK1)
        & v2_funct_1(X2)
        & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
        & k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)
        & v8_pre_topc(sK1)
        & v1_compts_1(sK0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ~ v3_tops_2(sK2,sK0,sK1)
      & v5_pre_topc(sK2,sK0,sK1)
      & v2_funct_1(sK2)
      & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      & k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      & v8_pre_topc(sK1)
      & v1_compts_1(sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_2(X2,X0,X1)
              & v5_pre_topc(X2,X0,X1)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              & v8_pre_topc(X1)
              & v1_compts_1(X0)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_2(X2,X0,X1)
              & v5_pre_topc(X2,X0,X1)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              & v8_pre_topc(X1)
              & v1_compts_1(X0)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
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
               => ( ( v5_pre_topc(X2,X0,X1)
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                    & v8_pre_topc(X1)
                    & v1_compts_1(X0) )
                 => v3_tops_2(X2,X0,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
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
             => ( ( v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & v8_pre_topc(X1)
                  & v1_compts_1(X0) )
               => v3_tops_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_compts_1)).

fof(f110,plain,(
    u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f70,f109])).

fof(f70,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f109,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unit_resulting_resolution,[],[f106,f74])).

fof(f74,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f106,plain,(
    l1_struct_0(sK1) ),
    inference(unit_resulting_resolution,[],[f63,f75])).

fof(f75,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f685,plain,(
    ! [X0] :
      ( k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X0)
      | ~ v2_funct_1(X0)
      | v3_tops_2(X0,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2))
      | k1_relat_1(sK2) != k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X0)
      | m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(k1_relat_1(sK2)))
      | ~ v1_funct_1(X0) ) ),
    inference(superposition,[],[f415,f121])).

fof(f415,plain,(
    ! [X142,X141] :
      ( k2_struct_0(X141) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(X141),X142)
      | ~ v2_funct_1(X142)
      | v3_tops_2(X142,sK0,X141)
      | ~ m1_subset_1(X142,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X141))))
      | v2_struct_0(X141)
      | ~ l1_pre_topc(X141)
      | ~ v1_funct_2(X142,k1_relat_1(sK2),u1_struct_0(X141))
      | k1_relat_1(sK2) != k1_relset_1(k1_relat_1(sK2),u1_struct_0(X141),X142)
      | m1_subset_1(sK4(sK0,X141,X142),k1_zfmisc_1(k1_relat_1(sK2)))
      | ~ v1_funct_1(X142) ) ),
    inference(global_subsumption,[],[f60,f414])).

fof(f414,plain,(
    ! [X142,X141] :
      ( k1_relat_1(sK2) != k1_relset_1(k1_relat_1(sK2),u1_struct_0(X141),X142)
      | m1_subset_1(sK4(sK0,X141,X142),k1_zfmisc_1(k1_relat_1(sK2)))
      | v3_tops_2(X142,sK0,X141)
      | ~ v2_funct_1(X142)
      | k2_struct_0(X141) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(X141),X142)
      | ~ m1_subset_1(X142,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X141))))
      | ~ v1_funct_2(X142,k1_relat_1(sK2),u1_struct_0(X141))
      | ~ v1_funct_1(X142)
      | ~ l1_pre_topc(X141)
      | v2_struct_0(X141)
      | ~ l1_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f341,f134])).

fof(f134,plain,(
    k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f107,f133])).

fof(f133,plain,(
    u1_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f124,f132])).

fof(f132,plain,(
    k1_relat_1(sK2) = k1_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(forward_demodulation,[],[f112,f121])).

fof(f112,plain,(
    k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f66,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f124,plain,(
    u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(backward_demodulation,[],[f108,f121])).

fof(f108,plain,(
    u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f69,f107])).

fof(f69,plain,(
    k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f107,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f105,f74])).

fof(f105,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f60,f75])).

fof(f341,plain,(
    ! [X142,X141] :
      ( m1_subset_1(sK4(sK0,X141,X142),k1_zfmisc_1(k1_relat_1(sK2)))
      | v3_tops_2(X142,sK0,X141)
      | ~ v2_funct_1(X142)
      | k2_struct_0(X141) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(X141),X142)
      | k2_struct_0(sK0) != k1_relset_1(k1_relat_1(sK2),u1_struct_0(X141),X142)
      | ~ m1_subset_1(X142,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X141))))
      | ~ v1_funct_2(X142,k1_relat_1(sK2),u1_struct_0(X141))
      | ~ v1_funct_1(X142)
      | ~ l1_pre_topc(X141)
      | v2_struct_0(X141)
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f85,f133])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v3_tops_2(X2,X0,X1)
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tops_2(X2,X0,X1)
                  | ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X1)
                      | ~ v4_pre_topc(sK4(X0,X1,X2),X0) )
                    & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X1)
                      | v4_pre_topc(sK4(X0,X1,X2),X0) )
                    & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v2_funct_1(X2)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                  | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                & ( ( ! [X4] :
                        ( ( ( v4_pre_topc(X4,X0)
                            | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1) )
                          & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1)
                            | ~ v4_pre_topc(X4,X0) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                  | ~ v3_tops_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f54,f55])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
            | ~ v4_pre_topc(X3,X0) )
          & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
            | v4_pre_topc(X3,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X1)
          | ~ v4_pre_topc(sK4(X0,X1,X2),X0) )
        & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X1)
          | v4_pre_topc(sK4(X0,X1,X2),X0) )
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tops_2(X2,X0,X1)
                  | ? [X3] :
                      ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                        | ~ v4_pre_topc(X3,X0) )
                      & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                        | v4_pre_topc(X3,X0) )
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v2_funct_1(X2)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                  | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                & ( ( ! [X4] :
                        ( ( ( v4_pre_topc(X4,X0)
                            | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1) )
                          & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1)
                            | ~ v4_pre_topc(X4,X0) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                  | ~ v3_tops_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tops_2(X2,X0,X1)
                  | ? [X3] :
                      ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                        | ~ v4_pre_topc(X3,X0) )
                      & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                        | v4_pre_topc(X3,X0) )
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v2_funct_1(X2)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                  | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                & ( ( ! [X3] :
                        ( ( ( v4_pre_topc(X3,X0)
                            | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) )
                          & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                            | ~ v4_pre_topc(X3,X0) ) )
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                  | ~ v3_tops_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tops_2(X2,X0,X1)
                  | ? [X3] :
                      ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                        | ~ v4_pre_topc(X3,X0) )
                      & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                        | v4_pre_topc(X3,X0) )
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v2_funct_1(X2)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                  | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                & ( ( ! [X3] :
                        ( ( ( v4_pre_topc(X3,X0)
                            | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) )
                          & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                            | ~ v4_pre_topc(X3,X0) ) )
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                  | ~ v3_tops_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( ( v4_pre_topc(X3,X0)
                      <=> v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) )
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( ( v4_pre_topc(X3,X0)
                      <=> v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) )
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_tops_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( v4_pre_topc(X3,X0)
                      <=> v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) ) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tops_2)).

fof(f60,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f61,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f63,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f138,plain,(
    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    inference(backward_demodulation,[],[f126,f133])).

fof(f126,plain,(
    k2_relat_1(sK2) = k2_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(backward_demodulation,[],[f113,f121])).

fof(f142,plain,(
    k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    inference(backward_demodulation,[],[f132,f133])).

fof(f137,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f123,f133])).

fof(f123,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f66,f121])).

fof(f136,plain,(
    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f122,f133])).

fof(f122,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f65,f121])).

fof(f65,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f47])).

fof(f73,plain,(
    ~ v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f71,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f64,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f111,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f66,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f773,plain,
    ( v4_pre_topc(k10_relat_1(sK2,k9_relat_1(sK2,sK4(sK0,sK1,sK2))),sK0)
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f772,f139])).

fof(f139,plain,(
    ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,X0) ),
    inference(backward_demodulation,[],[f128,f133])).

fof(f128,plain,(
    ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2,X0) ),
    inference(backward_demodulation,[],[f117,f121])).

fof(f117,plain,(
    ! [X0] : k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(unit_resulting_resolution,[],[f66,f101])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f772,plain,
    ( v4_pre_topc(k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,k9_relat_1(sK2,sK4(sK0,sK1,sK2))),sK0)
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f64,f72,f136,f137,f131,f731,f605])).

fof(f605,plain,(
    ! [X2,X3] :
      ( v4_pre_topc(k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X2,X3),sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
      | ~ v1_funct_1(X2)
      | ~ v5_pre_topc(X2,sK0,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_relat_1(sK2)))
      | ~ v4_pre_topc(X3,sK1)
      | ~ v1_funct_2(X2,k1_relat_1(sK2),k2_relat_1(sK2)) ) ),
    inference(global_subsumption,[],[f60,f602])).

fof(f602,plain,(
    ! [X2,X3] :
      ( v4_pre_topc(k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X2,X3),sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_2(X2,k1_relat_1(sK2),k2_relat_1(sK2))
      | ~ v4_pre_topc(X3,sK1)
      | ~ v5_pre_topc(X2,sK0,sK1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_relat_1(sK2))) ) ),
    inference(superposition,[],[f242,f133])).

fof(f242,plain,(
    ! [X17,X15,X16] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(X15),k2_relat_1(sK2),X16,X17),X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),k2_relat_1(sK2))))
      | ~ l1_pre_topc(X15)
      | ~ v1_funct_2(X16,u1_struct_0(X15),k2_relat_1(sK2))
      | ~ v4_pre_topc(X17,sK1)
      | ~ v5_pre_topc(X16,X15,sK1)
      | ~ v1_funct_1(X16)
      | ~ m1_subset_1(X17,k1_zfmisc_1(k2_relat_1(sK2))) ) ),
    inference(global_subsumption,[],[f63,f156])).

fof(f156,plain,(
    ! [X17,X15,X16] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(X15),k2_relat_1(sK2),X16,X17),X15)
      | ~ v4_pre_topc(X17,sK1)
      | ~ m1_subset_1(X17,k1_zfmisc_1(k2_relat_1(sK2)))
      | ~ v5_pre_topc(X16,X15,sK1)
      | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),k2_relat_1(sK2))))
      | ~ v1_funct_2(X16,u1_struct_0(X15),k2_relat_1(sK2))
      | ~ v1_funct_1(X16)
      | ~ l1_pre_topc(sK1)
      | ~ l1_pre_topc(X15) ) ),
    inference(superposition,[],[f76,f121])).

fof(f76,plain,(
    ! [X4,X2,X0,X1] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),X0)
                    & v4_pre_topc(sK3(X0,X1,X2),X1)
                    & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f49,f50])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),X0)
        & v4_pre_topc(sK3(X0,X1,X2),X1)
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_pre_topc)).

fof(f731,plain,
    ( v4_pre_topc(k9_relat_1(sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f729])).

fof(f729,plain,
    ( spl5_14
  <=> v4_pre_topc(k9_relat_1(sK2,sK4(sK0,sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f131,plain,(
    ! [X0] : m1_subset_1(k9_relat_1(sK2,X0),k1_zfmisc_1(k2_relat_1(sK2))) ),
    inference(backward_demodulation,[],[f120,f121])).

fof(f120,plain,(
    ! [X0] : m1_subset_1(k9_relat_1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f116,f118])).

fof(f118,plain,(
    ! [X0] : k9_relat_1(sK2,X0) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) ),
    inference(unit_resulting_resolution,[],[f66,f102])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f116,plain,(
    ! [X0] : m1_subset_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unit_resulting_resolution,[],[f66,f100])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f72,plain,(
    v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f726,plain,
    ( ~ v4_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f725])).

fof(f725,plain,
    ( spl5_13
  <=> v4_pre_topc(sK4(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f764,plain,(
    ~ spl5_13 ),
    inference(avatar_contradiction_clause,[],[f762])).

fof(f762,plain,
    ( $false
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f727,f690,f757,f682])).

fof(f682,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_relat_1(sK2)))
      | v4_pre_topc(k9_relat_1(sK2,X2),sK1)
      | ~ v4_pre_topc(X2,sK0) ) ),
    inference(global_subsumption,[],[f72,f64,f136,f137,f681])).

fof(f681,plain,(
    ! [X2] :
      ( v4_pre_topc(k9_relat_1(sK2,X2),sK1)
      | ~ v4_pre_topc(X2,sK0)
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_relat_1(sK2)))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ) ),
    inference(forward_demodulation,[],[f680,f140])).

fof(f140,plain,(
    ! [X0] : k9_relat_1(sK2,X0) = k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,X0) ),
    inference(backward_demodulation,[],[f129,f133])).

fof(f129,plain,(
    ! [X0] : k9_relat_1(sK2,X0) = k7_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2,X0) ),
    inference(backward_demodulation,[],[f118,f121])).

fof(f680,plain,(
    ! [X2] :
      ( ~ v4_pre_topc(X2,sK0)
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
      | v4_pre_topc(k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,X2),sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_relat_1(sK2)))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ) ),
    inference(trivial_inequality_removal,[],[f679])).

fof(f679,plain,(
    ! [X2] :
      ( k2_relat_1(sK2) != k2_relat_1(sK2)
      | ~ v4_pre_topc(X2,sK0)
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
      | v4_pre_topc(k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,X2),sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_relat_1(sK2)))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ) ),
    inference(superposition,[],[f675,f138])).

fof(f675,plain,(
    ! [X2,X3] :
      ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X2)
      | ~ v4_pre_topc(X3,sK0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
      | v4_pre_topc(k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X2,X3),sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_relat_1(sK2)))
      | ~ v5_pre_topc(X2,sK0,sK1)
      | ~ v1_funct_2(X2,k1_relat_1(sK2),k2_relat_1(sK2)) ) ),
    inference(global_subsumption,[],[f67,f60,f59,f672])).

fof(f672,plain,(
    ! [X2,X3] :
      ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X2)
      | v4_pre_topc(k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X2,X3),sK1)
      | ~ v1_compts_1(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
      | ~ v5_pre_topc(X2,sK0,sK1)
      | ~ v1_funct_2(X2,k1_relat_1(sK2),k2_relat_1(sK2))
      | ~ v1_funct_1(X2)
      | ~ v2_pre_topc(sK0)
      | ~ v4_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_relat_1(sK2))) ) ),
    inference(superposition,[],[f280,f133])).

fof(f280,plain,(
    ! [X187,X188,X186] :
      ( k2_relat_1(sK2) != k2_relset_1(u1_struct_0(X186),k2_relat_1(sK2),X187)
      | v4_pre_topc(k7_relset_1(u1_struct_0(X186),k2_relat_1(sK2),X187,X188),sK1)
      | ~ v1_compts_1(X186)
      | ~ l1_pre_topc(X186)
      | ~ m1_subset_1(X187,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X186),k2_relat_1(sK2))))
      | ~ v5_pre_topc(X187,X186,sK1)
      | ~ v1_funct_2(X187,u1_struct_0(X186),k2_relat_1(sK2))
      | ~ v1_funct_1(X187)
      | ~ v2_pre_topc(X186)
      | ~ v4_pre_topc(X188,X186)
      | ~ m1_subset_1(X188,k1_zfmisc_1(u1_struct_0(X186))) ) ),
    inference(global_subsumption,[],[f68,f63,f62,f61,f279])).

fof(f279,plain,(
    ! [X187,X188,X186] :
      ( k2_relat_1(sK2) != k2_relset_1(u1_struct_0(X186),k2_relat_1(sK2),X187)
      | v4_pre_topc(k7_relset_1(u1_struct_0(X186),k2_relat_1(sK2),X187,X188),sK1)
      | ~ v4_pre_topc(X188,X186)
      | ~ m1_subset_1(X188,k1_zfmisc_1(u1_struct_0(X186)))
      | ~ v5_pre_topc(X187,X186,sK1)
      | ~ v8_pre_topc(sK1)
      | ~ v1_compts_1(X186)
      | ~ m1_subset_1(X187,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X186),k2_relat_1(sK2))))
      | ~ v1_funct_2(X187,u1_struct_0(X186),k2_relat_1(sK2))
      | ~ v1_funct_1(X187)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X186)
      | ~ v2_pre_topc(X186) ) ),
    inference(forward_demodulation,[],[f233,f125])).

fof(f233,plain,(
    ! [X187,X188,X186] :
      ( v4_pre_topc(k7_relset_1(u1_struct_0(X186),k2_relat_1(sK2),X187,X188),sK1)
      | ~ v4_pre_topc(X188,X186)
      | ~ m1_subset_1(X188,k1_zfmisc_1(u1_struct_0(X186)))
      | ~ v5_pre_topc(X187,X186,sK1)
      | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X186),k2_relat_1(sK2),X187)
      | ~ v8_pre_topc(sK1)
      | ~ v1_compts_1(X186)
      | ~ m1_subset_1(X187,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X186),k2_relat_1(sK2))))
      | ~ v1_funct_2(X187,u1_struct_0(X186),k2_relat_1(sK2))
      | ~ v1_funct_1(X187)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X186)
      | ~ v2_pre_topc(X186) ) ),
    inference(superposition,[],[f88,f121])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v5_pre_topc(X2,X0,X1)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ v8_pre_topc(X1)
      | ~ v1_compts_1(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v5_pre_topc(X2,X0,X1)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ v8_pre_topc(X1)
              | ~ v1_compts_1(X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v5_pre_topc(X2,X0,X1)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ v8_pre_topc(X1)
              | ~ v1_compts_1(X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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
             => ( ( v5_pre_topc(X2,X0,X1)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & v8_pre_topc(X1)
                  & v1_compts_1(X0) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( v4_pre_topc(X3,X0)
                     => v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_compts_1)).

fof(f62,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f68,plain,(
    v8_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f59,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f67,plain,(
    v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f757,plain,
    ( ~ v4_pre_topc(k9_relat_1(sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f751,f140])).

fof(f751,plain,
    ( ~ v4_pre_topc(k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f64,f71,f73,f727,f136,f137,f142,f138,f748])).

fof(f748,plain,(
    ! [X1] :
      ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X1)
      | ~ v4_pre_topc(k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X1,sK4(sK0,sK1,X1)),sK1)
      | ~ v1_funct_1(X1)
      | v3_tops_2(X1,sK0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
      | ~ v1_funct_2(X1,k1_relat_1(sK2),k2_relat_1(sK2))
      | ~ v2_funct_1(X1)
      | ~ v4_pre_topc(sK4(sK0,sK1,X1),sK0)
      | k1_relat_1(sK2) != k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X1) ) ),
    inference(global_subsumption,[],[f60,f747])).

fof(f747,plain,(
    ! [X1] :
      ( k1_relat_1(sK2) != k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_2(X1,k1_relat_1(sK2),k2_relat_1(sK2))
      | ~ v4_pre_topc(sK4(sK0,sK1,X1),sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
      | v3_tops_2(X1,sK0,sK1)
      | ~ v4_pre_topc(k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X1,sK4(sK0,sK1,X1)),sK1)
      | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X1) ) ),
    inference(forward_demodulation,[],[f742,f134])).

fof(f742,plain,(
    ! [X1] :
      ( k2_struct_0(sK0) != k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_2(X1,k1_relat_1(sK2),k2_relat_1(sK2))
      | ~ v4_pre_topc(sK4(sK0,sK1,X1),sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
      | v3_tops_2(X1,sK0,sK1)
      | ~ v4_pre_topc(k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X1,sK4(sK0,sK1,X1)),sK1)
      | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X1) ) ),
    inference(superposition,[],[f269,f133])).

fof(f269,plain,(
    ! [X182,X181] :
      ( k2_struct_0(X181) != k1_relset_1(u1_struct_0(X181),k2_relat_1(sK2),X182)
      | ~ v1_funct_1(X182)
      | ~ v2_funct_1(X182)
      | ~ v1_funct_2(X182,u1_struct_0(X181),k2_relat_1(sK2))
      | ~ v4_pre_topc(sK4(X181,sK1,X182),X181)
      | ~ l1_pre_topc(X181)
      | ~ m1_subset_1(X182,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X181),k2_relat_1(sK2))))
      | v3_tops_2(X182,X181,sK1)
      | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X181),k2_relat_1(sK2),X182,sK4(X181,sK1,X182)),sK1)
      | k2_relat_1(sK2) != k2_relset_1(u1_struct_0(X181),k2_relat_1(sK2),X182) ) ),
    inference(global_subsumption,[],[f63,f61,f268])).

fof(f268,plain,(
    ! [X182,X181] :
      ( k2_relat_1(sK2) != k2_relset_1(u1_struct_0(X181),k2_relat_1(sK2),X182)
      | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X181),k2_relat_1(sK2),X182,sK4(X181,sK1,X182)),sK1)
      | v3_tops_2(X182,X181,sK1)
      | ~ v4_pre_topc(sK4(X181,sK1,X182),X181)
      | ~ v2_funct_1(X182)
      | k2_struct_0(X181) != k1_relset_1(u1_struct_0(X181),k2_relat_1(sK2),X182)
      | ~ m1_subset_1(X182,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X181),k2_relat_1(sK2))))
      | ~ v1_funct_2(X182,u1_struct_0(X181),k2_relat_1(sK2))
      | ~ v1_funct_1(X182)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X181) ) ),
    inference(forward_demodulation,[],[f231,f125])).

fof(f231,plain,(
    ! [X182,X181] :
      ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X181),k2_relat_1(sK2),X182,sK4(X181,sK1,X182)),sK1)
      | v3_tops_2(X182,X181,sK1)
      | ~ v4_pre_topc(sK4(X181,sK1,X182),X181)
      | ~ v2_funct_1(X182)
      | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X181),k2_relat_1(sK2),X182)
      | k2_struct_0(X181) != k1_relset_1(u1_struct_0(X181),k2_relat_1(sK2),X182)
      | ~ m1_subset_1(X182,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X181),k2_relat_1(sK2))))
      | ~ v1_funct_2(X182,u1_struct_0(X181),k2_relat_1(sK2))
      | ~ v1_funct_1(X182)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X181) ) ),
    inference(superposition,[],[f87,f121])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v3_tops_2(X2,X0,X1)
      | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X1)
      | ~ v4_pre_topc(sK4(X0,X1,X2),X0)
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f727,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f725])).

fof(f732,plain,
    ( spl5_13
    | spl5_14 ),
    inference(avatar_split_clause,[],[f723,f729,f725])).

fof(f723,plain,
    ( v4_pre_topc(k9_relat_1(sK2,sK4(sK0,sK1,sK2)),sK1)
    | v4_pre_topc(sK4(sK0,sK1,sK2),sK0) ),
    inference(global_subsumption,[],[f73,f71,f64,f136,f137,f722])).

fof(f722,plain,
    ( v4_pre_topc(k9_relat_1(sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | v3_tops_2(sK2,sK0,sK1)
    | v4_pre_topc(sK4(sK0,sK1,sK2),sK0) ),
    inference(forward_demodulation,[],[f721,f140])).

fof(f721,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | v4_pre_topc(k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | v3_tops_2(sK2,sK0,sK1)
    | v4_pre_topc(sK4(sK0,sK1,sK2),sK0) ),
    inference(trivial_inequality_removal,[],[f720])).

fof(f720,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | v4_pre_topc(k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | v3_tops_2(sK2,sK0,sK1)
    | v4_pre_topc(sK4(sK0,sK1,sK2),sK0) ),
    inference(forward_demodulation,[],[f719,f142])).

fof(f719,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k1_relat_1(sK2) != k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | v4_pre_topc(k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | v3_tops_2(sK2,sK0,sK1)
    | v4_pre_topc(sK4(sK0,sK1,sK2),sK0) ),
    inference(trivial_inequality_removal,[],[f718])).

fof(f718,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k1_relat_1(sK2) != k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | v4_pre_topc(k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | v3_tops_2(sK2,sK0,sK1)
    | v4_pre_topc(sK4(sK0,sK1,sK2),sK0) ),
    inference(superposition,[],[f712,f138])).

fof(f712,plain,(
    ! [X1] :
      ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
      | k1_relat_1(sK2) != k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X1)
      | v4_pre_topc(k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X1,sK4(sK0,sK1,X1)),sK1)
      | ~ v1_funct_2(X1,k1_relat_1(sK2),k2_relat_1(sK2))
      | v3_tops_2(X1,sK0,sK1)
      | v4_pre_topc(sK4(sK0,sK1,X1),sK0) ) ),
    inference(global_subsumption,[],[f60,f711])).

fof(f711,plain,(
    ! [X1] :
      ( k1_relat_1(sK2) != k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X1)
      | v4_pre_topc(sK4(sK0,sK1,X1),sK0)
      | v3_tops_2(X1,sK0,sK1)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
      | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X1)
      | v4_pre_topc(k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X1,sK4(sK0,sK1,X1)),sK1)
      | ~ v1_funct_2(X1,k1_relat_1(sK2),k2_relat_1(sK2)) ) ),
    inference(forward_demodulation,[],[f706,f134])).

fof(f706,plain,(
    ! [X1] :
      ( k2_struct_0(sK0) != k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X1)
      | v4_pre_topc(sK4(sK0,sK1,X1),sK0)
      | v3_tops_2(X1,sK0,sK1)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
      | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X1)
      | v4_pre_topc(k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X1,sK4(sK0,sK1,X1)),sK1)
      | ~ v1_funct_2(X1,k1_relat_1(sK2),k2_relat_1(sK2)) ) ),
    inference(superposition,[],[f265,f133])).

fof(f265,plain,(
    ! [X161,X162] :
      ( k2_struct_0(X161) != k1_relset_1(u1_struct_0(X161),k2_relat_1(sK2),X162)
      | v4_pre_topc(sK4(X161,sK1,X162),X161)
      | v3_tops_2(X162,X161,sK1)
      | ~ v2_funct_1(X162)
      | ~ v1_funct_1(X162)
      | ~ l1_pre_topc(X161)
      | ~ m1_subset_1(X162,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X161),k2_relat_1(sK2))))
      | k2_relat_1(sK2) != k2_relset_1(u1_struct_0(X161),k2_relat_1(sK2),X162)
      | v4_pre_topc(k7_relset_1(u1_struct_0(X161),k2_relat_1(sK2),X162,sK4(X161,sK1,X162)),sK1)
      | ~ v1_funct_2(X162,u1_struct_0(X161),k2_relat_1(sK2)) ) ),
    inference(global_subsumption,[],[f63,f61,f264])).

fof(f264,plain,(
    ! [X161,X162] :
      ( k2_relat_1(sK2) != k2_relset_1(u1_struct_0(X161),k2_relat_1(sK2),X162)
      | v4_pre_topc(k7_relset_1(u1_struct_0(X161),k2_relat_1(sK2),X162,sK4(X161,sK1,X162)),sK1)
      | v3_tops_2(X162,X161,sK1)
      | v4_pre_topc(sK4(X161,sK1,X162),X161)
      | ~ v2_funct_1(X162)
      | k2_struct_0(X161) != k1_relset_1(u1_struct_0(X161),k2_relat_1(sK2),X162)
      | ~ m1_subset_1(X162,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X161),k2_relat_1(sK2))))
      | ~ v1_funct_2(X162,u1_struct_0(X161),k2_relat_1(sK2))
      | ~ v1_funct_1(X162)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X161) ) ),
    inference(forward_demodulation,[],[f221,f125])).

fof(f221,plain,(
    ! [X161,X162] :
      ( v4_pre_topc(k7_relset_1(u1_struct_0(X161),k2_relat_1(sK2),X162,sK4(X161,sK1,X162)),sK1)
      | v3_tops_2(X162,X161,sK1)
      | v4_pre_topc(sK4(X161,sK1,X162),X161)
      | ~ v2_funct_1(X162)
      | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X161),k2_relat_1(sK2),X162)
      | k2_struct_0(X161) != k1_relset_1(u1_struct_0(X161),k2_relat_1(sK2),X162)
      | ~ m1_subset_1(X162,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X161),k2_relat_1(sK2))))
      | ~ v1_funct_2(X162,u1_struct_0(X161),k2_relat_1(sK2))
      | ~ v1_funct_1(X162)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X161) ) ),
    inference(superposition,[],[f86,f121])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v3_tops_2(X2,X0,X1)
      | v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X1)
      | v4_pre_topc(sK4(X0,X1,X2),X0)
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:51:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (24633)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.45  % (24633)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f783,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f732,f764,f780])).
% 0.21/0.45  fof(f780,plain,(
% 0.21/0.45    spl5_13 | ~spl5_14),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f776])).
% 0.21/0.45  fof(f776,plain,(
% 0.21/0.45    $false | (spl5_13 | ~spl5_14)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f726,f774])).
% 0.21/0.45  fof(f774,plain,(
% 0.21/0.45    v4_pre_topc(sK4(sK0,sK1,sK2),sK0) | ~spl5_14),
% 0.21/0.45    inference(forward_demodulation,[],[f773,f698])).
% 0.21/0.45  fof(f698,plain,(
% 0.21/0.45    sK4(sK0,sK1,sK2) = k10_relat_1(sK2,k9_relat_1(sK2,sK4(sK0,sK1,sK2)))),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f111,f64,f71,f696,f89])).
% 0.21/0.45  fof(f89,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f31])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(flattening,[],[f30])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.45    inference(ennf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).
% 0.21/0.45  fof(f696,plain,(
% 0.21/0.45    r1_tarski(sK4(sK0,sK1,sK2),k1_relat_1(sK2))),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f690,f94])).
% 0.21/0.45  fof(f94,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f36])).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.45    inference(ennf_transformation,[],[f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.21/0.45    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.45  fof(f690,plain,(
% 0.21/0.45    m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(k1_relat_1(sK2)))),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f64,f71,f73,f136,f137,f142,f138,f689])).
% 0.21/0.45  fof(f689,plain,(
% 0.21/0.45    ( ! [X0] : (k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X0) | m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(k1_relat_1(sK2))) | ~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | k1_relat_1(sK2) != k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X0) | v3_tops_2(X0,sK0,sK1) | ~v2_funct_1(X0) | ~v1_funct_1(X0)) )),
% 0.21/0.45    inference(global_subsumption,[],[f63,f61,f688])).
% 0.21/0.45  fof(f688,plain,(
% 0.21/0.45    ( ! [X0] : (k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X0) | ~v2_funct_1(X0) | v3_tops_2(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) | k1_relat_1(sK2) != k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X0) | m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(k1_relat_1(sK2))) | ~v1_funct_1(X0)) )),
% 0.21/0.45    inference(forward_demodulation,[],[f685,f125])).
% 0.21/0.45  fof(f125,plain,(
% 0.21/0.45    k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.21/0.45    inference(backward_demodulation,[],[f109,f121])).
% 0.21/0.45  fof(f121,plain,(
% 0.21/0.45    u1_struct_0(sK1) = k2_relat_1(sK2)),
% 0.21/0.45    inference(backward_demodulation,[],[f110,f113])).
% 0.21/0.45  fof(f113,plain,(
% 0.21/0.45    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f66,f97])).
% 0.21/0.45  fof(f97,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f39])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(ennf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.45  fof(f66,plain,(
% 0.21/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.45    inference(cnf_transformation,[],[f47])).
% 0.21/0.45  fof(f47,plain,(
% 0.21/0.45    ((~v3_tops_2(sK2,sK0,sK1) & v5_pre_topc(sK2,sK0,sK1) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & v8_pre_topc(sK1) & v1_compts_1(sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f46,f45,f44])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (? [X2] : (~v3_tops_2(X2,X0,X1) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & v8_pre_topc(X1) & v1_compts_1(X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v3_tops_2(X2,sK0,X1) & v5_pre_topc(X2,sK0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & v8_pre_topc(X1) & v1_compts_1(sK0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f45,plain,(
% 0.21/0.45    ? [X1] : (? [X2] : (~v3_tops_2(X2,sK0,X1) & v5_pre_topc(X2,sK0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & v8_pre_topc(X1) & v1_compts_1(sK0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (~v3_tops_2(X2,sK0,sK1) & v5_pre_topc(X2,sK0,sK1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) & v8_pre_topc(sK1) & v1_compts_1(sK0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    ? [X2] : (~v3_tops_2(X2,sK0,sK1) & v5_pre_topc(X2,sK0,sK1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) & v8_pre_topc(sK1) & v1_compts_1(sK0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (~v3_tops_2(sK2,sK0,sK1) & v5_pre_topc(sK2,sK0,sK1) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & v8_pre_topc(sK1) & v1_compts_1(sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (? [X2] : (~v3_tops_2(X2,X0,X1) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & v8_pre_topc(X1) & v1_compts_1(X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.45    inference(flattening,[],[f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (? [X2] : ((~v3_tops_2(X2,X0,X1) & (v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & v8_pre_topc(X1) & v1_compts_1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f18])).
% 0.21/0.45  fof(f18,negated_conjecture,(
% 0.21/0.45    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & v8_pre_topc(X1) & v1_compts_1(X0)) => v3_tops_2(X2,X0,X1)))))),
% 0.21/0.45    inference(negated_conjecture,[],[f17])).
% 0.21/0.45  fof(f17,conjecture,(
% 0.21/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & v8_pre_topc(X1) & v1_compts_1(X0)) => v3_tops_2(X2,X0,X1)))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_compts_1)).
% 0.21/0.45  fof(f110,plain,(
% 0.21/0.45    u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.45    inference(backward_demodulation,[],[f70,f109])).
% 0.21/0.45  fof(f70,plain,(
% 0.21/0.45    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f47])).
% 0.21/0.45  fof(f109,plain,(
% 0.21/0.45    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f106,f74])).
% 0.21/0.45  fof(f74,plain,(
% 0.21/0.45    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f22])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f13])).
% 0.21/0.45  fof(f13,axiom,(
% 0.21/0.45    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.45  fof(f106,plain,(
% 0.21/0.45    l1_struct_0(sK1)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f63,f75])).
% 0.21/0.45  fof(f75,plain,(
% 0.21/0.45    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f23])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f14])).
% 0.21/0.45  fof(f14,axiom,(
% 0.21/0.45    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.45  fof(f685,plain,(
% 0.21/0.45    ( ! [X0] : (k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X0) | ~v2_funct_1(X0) | v3_tops_2(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) | k1_relat_1(sK2) != k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X0) | m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(k1_relat_1(sK2))) | ~v1_funct_1(X0)) )),
% 0.21/0.45    inference(superposition,[],[f415,f121])).
% 0.21/0.45  fof(f415,plain,(
% 0.21/0.45    ( ! [X142,X141] : (k2_struct_0(X141) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(X141),X142) | ~v2_funct_1(X142) | v3_tops_2(X142,sK0,X141) | ~m1_subset_1(X142,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X141)))) | v2_struct_0(X141) | ~l1_pre_topc(X141) | ~v1_funct_2(X142,k1_relat_1(sK2),u1_struct_0(X141)) | k1_relat_1(sK2) != k1_relset_1(k1_relat_1(sK2),u1_struct_0(X141),X142) | m1_subset_1(sK4(sK0,X141,X142),k1_zfmisc_1(k1_relat_1(sK2))) | ~v1_funct_1(X142)) )),
% 0.21/0.45    inference(global_subsumption,[],[f60,f414])).
% 0.21/0.45  fof(f414,plain,(
% 0.21/0.45    ( ! [X142,X141] : (k1_relat_1(sK2) != k1_relset_1(k1_relat_1(sK2),u1_struct_0(X141),X142) | m1_subset_1(sK4(sK0,X141,X142),k1_zfmisc_1(k1_relat_1(sK2))) | v3_tops_2(X142,sK0,X141) | ~v2_funct_1(X142) | k2_struct_0(X141) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(X141),X142) | ~m1_subset_1(X142,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X141)))) | ~v1_funct_2(X142,k1_relat_1(sK2),u1_struct_0(X141)) | ~v1_funct_1(X142) | ~l1_pre_topc(X141) | v2_struct_0(X141) | ~l1_pre_topc(sK0)) )),
% 0.21/0.45    inference(forward_demodulation,[],[f341,f134])).
% 0.21/0.45  fof(f134,plain,(
% 0.21/0.45    k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.21/0.45    inference(backward_demodulation,[],[f107,f133])).
% 0.21/0.45  fof(f133,plain,(
% 0.21/0.45    u1_struct_0(sK0) = k1_relat_1(sK2)),
% 0.21/0.45    inference(backward_demodulation,[],[f124,f132])).
% 0.21/0.45  fof(f132,plain,(
% 0.21/0.45    k1_relat_1(sK2) = k1_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.21/0.45    inference(forward_demodulation,[],[f112,f121])).
% 0.21/0.45  fof(f112,plain,(
% 0.21/0.45    k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f66,f96])).
% 0.21/0.45  fof(f96,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f38])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(ennf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.45  fof(f124,plain,(
% 0.21/0.45    u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.21/0.45    inference(backward_demodulation,[],[f108,f121])).
% 0.21/0.45  fof(f108,plain,(
% 0.21/0.45    u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.45    inference(backward_demodulation,[],[f69,f107])).
% 0.21/0.45  fof(f69,plain,(
% 0.21/0.45    k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f47])).
% 0.21/0.45  fof(f107,plain,(
% 0.21/0.45    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f105,f74])).
% 0.21/0.45  fof(f105,plain,(
% 0.21/0.45    l1_struct_0(sK0)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f60,f75])).
% 0.21/0.45  fof(f341,plain,(
% 0.21/0.45    ( ! [X142,X141] : (m1_subset_1(sK4(sK0,X141,X142),k1_zfmisc_1(k1_relat_1(sK2))) | v3_tops_2(X142,sK0,X141) | ~v2_funct_1(X142) | k2_struct_0(X141) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(X141),X142) | k2_struct_0(sK0) != k1_relset_1(k1_relat_1(sK2),u1_struct_0(X141),X142) | ~m1_subset_1(X142,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X141)))) | ~v1_funct_2(X142,k1_relat_1(sK2),u1_struct_0(X141)) | ~v1_funct_1(X142) | ~l1_pre_topc(X141) | v2_struct_0(X141) | ~l1_pre_topc(sK0)) )),
% 0.21/0.45    inference(superposition,[],[f85,f133])).
% 0.21/0.45  fof(f85,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (v3_tops_2(X2,X0,X1) | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f56])).
% 0.21/0.45  fof(f56,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | ((~v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X1) | ~v4_pre_topc(sK4(X0,X1,X2),X0)) & (v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X1) | v4_pre_topc(sK4(X0,X1,X2),X0)) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) & ((! [X4] : (((v4_pre_topc(X4,X0) | ~v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1)) & (v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1) | ~v4_pre_topc(X4,X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f54,f55])).
% 0.21/0.45  fof(f55,plain,(
% 0.21/0.45    ! [X2,X1,X0] : (? [X3] : ((~v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) | ~v4_pre_topc(X3,X0)) & (v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) | v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => ((~v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X1) | ~v4_pre_topc(sK4(X0,X1,X2),X0)) & (v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X1) | v4_pre_topc(sK4(X0,X1,X2),X0)) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | ? [X3] : ((~v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) | ~v4_pre_topc(X3,X0)) & (v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) | v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) & ((! [X4] : (((v4_pre_topc(X4,X0) | ~v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1)) & (v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1) | ~v4_pre_topc(X4,X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(rectify,[],[f53])).
% 0.21/0.45  fof(f53,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | ? [X3] : ((~v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) | ~v4_pre_topc(X3,X0)) & (v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) | v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) & ((! [X3] : (((v4_pre_topc(X3,X0) | ~v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)) & (v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) | ~v4_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(flattening,[],[f52])).
% 0.21/0.45  fof(f52,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | (? [X3] : (((~v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) | ~v4_pre_topc(X3,X0)) & (v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) | v4_pre_topc(X3,X0))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) & ((! [X3] : (((v4_pre_topc(X3,X0) | ~v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)) & (v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) | ~v4_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(nnf_transformation,[],[f27])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (! [X3] : ((v4_pre_topc(X3,X0) <=> v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(flattening,[],[f26])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (! [X3] : ((v4_pre_topc(X3,X0) <=> v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | v2_struct_0(X1))) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f15])).
% 0.21/0.45  fof(f15,axiom,(
% 0.21/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X3,X0) <=> v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tops_2)).
% 0.21/0.45  fof(f60,plain,(
% 0.21/0.45    l1_pre_topc(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f47])).
% 0.21/0.45  fof(f61,plain,(
% 0.21/0.45    ~v2_struct_0(sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f47])).
% 0.21/0.45  fof(f63,plain,(
% 0.21/0.45    l1_pre_topc(sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f47])).
% 0.21/0.45  fof(f138,plain,(
% 0.21/0.45    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.21/0.45    inference(backward_demodulation,[],[f126,f133])).
% 0.21/0.45  fof(f126,plain,(
% 0.21/0.45    k2_relat_1(sK2) = k2_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.21/0.45    inference(backward_demodulation,[],[f113,f121])).
% 0.21/0.45  fof(f142,plain,(
% 0.21/0.45    k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.21/0.45    inference(backward_demodulation,[],[f132,f133])).
% 0.21/0.45  fof(f137,plain,(
% 0.21/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.21/0.45    inference(backward_demodulation,[],[f123,f133])).
% 0.21/0.45  fof(f123,plain,(
% 0.21/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2))))),
% 0.21/0.45    inference(backward_demodulation,[],[f66,f121])).
% 0.21/0.45  fof(f136,plain,(
% 0.21/0.45    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 0.21/0.45    inference(backward_demodulation,[],[f122,f133])).
% 0.21/0.45  fof(f122,plain,(
% 0.21/0.45    v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2))),
% 0.21/0.45    inference(backward_demodulation,[],[f65,f121])).
% 0.21/0.45  fof(f65,plain,(
% 0.21/0.45    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.45    inference(cnf_transformation,[],[f47])).
% 0.21/0.45  fof(f73,plain,(
% 0.21/0.45    ~v3_tops_2(sK2,sK0,sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f47])).
% 0.21/0.45  fof(f71,plain,(
% 0.21/0.45    v2_funct_1(sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f47])).
% 0.21/0.45  fof(f64,plain,(
% 0.21/0.45    v1_funct_1(sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f47])).
% 0.21/0.45  fof(f111,plain,(
% 0.21/0.45    v1_relat_1(sK2)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f66,f95])).
% 0.21/0.45  fof(f95,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f37])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(ennf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.45  fof(f773,plain,(
% 0.21/0.45    v4_pre_topc(k10_relat_1(sK2,k9_relat_1(sK2,sK4(sK0,sK1,sK2))),sK0) | ~spl5_14),
% 0.21/0.45    inference(forward_demodulation,[],[f772,f139])).
% 0.21/0.45  fof(f139,plain,(
% 0.21/0.45    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,X0)) )),
% 0.21/0.45    inference(backward_demodulation,[],[f128,f133])).
% 0.21/0.45  fof(f128,plain,(
% 0.21/0.45    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2,X0)) )),
% 0.21/0.45    inference(backward_demodulation,[],[f117,f121])).
% 0.21/0.45  fof(f117,plain,(
% 0.21/0.45    ( ! [X0] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0)) )),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f66,f101])).
% 0.21/0.45  fof(f101,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f42])).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(ennf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.45  fof(f772,plain,(
% 0.21/0.45    v4_pre_topc(k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,k9_relat_1(sK2,sK4(sK0,sK1,sK2))),sK0) | ~spl5_14),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f64,f72,f136,f137,f131,f731,f605])).
% 0.21/0.45  fof(f605,plain,(
% 0.21/0.45    ( ! [X2,X3] : (v4_pre_topc(k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X2,X3),sK0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_1(X2) | ~v5_pre_topc(X2,sK0,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_relat_1(sK2))) | ~v4_pre_topc(X3,sK1) | ~v1_funct_2(X2,k1_relat_1(sK2),k2_relat_1(sK2))) )),
% 0.21/0.45    inference(global_subsumption,[],[f60,f602])).
% 0.21/0.45  fof(f602,plain,(
% 0.21/0.45    ( ! [X2,X3] : (v4_pre_topc(k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X2,X3),sK0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~l1_pre_topc(sK0) | ~v1_funct_2(X2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v4_pre_topc(X3,sK1) | ~v5_pre_topc(X2,sK0,sK1) | ~v1_funct_1(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_relat_1(sK2)))) )),
% 0.21/0.45    inference(superposition,[],[f242,f133])).
% 0.21/0.45  fof(f242,plain,(
% 0.21/0.45    ( ! [X17,X15,X16] : (v4_pre_topc(k8_relset_1(u1_struct_0(X15),k2_relat_1(sK2),X16,X17),X15) | ~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),k2_relat_1(sK2)))) | ~l1_pre_topc(X15) | ~v1_funct_2(X16,u1_struct_0(X15),k2_relat_1(sK2)) | ~v4_pre_topc(X17,sK1) | ~v5_pre_topc(X16,X15,sK1) | ~v1_funct_1(X16) | ~m1_subset_1(X17,k1_zfmisc_1(k2_relat_1(sK2)))) )),
% 0.21/0.45    inference(global_subsumption,[],[f63,f156])).
% 0.21/0.45  fof(f156,plain,(
% 0.21/0.45    ( ! [X17,X15,X16] : (v4_pre_topc(k8_relset_1(u1_struct_0(X15),k2_relat_1(sK2),X16,X17),X15) | ~v4_pre_topc(X17,sK1) | ~m1_subset_1(X17,k1_zfmisc_1(k2_relat_1(sK2))) | ~v5_pre_topc(X16,X15,sK1) | ~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),k2_relat_1(sK2)))) | ~v1_funct_2(X16,u1_struct_0(X15),k2_relat_1(sK2)) | ~v1_funct_1(X16) | ~l1_pre_topc(sK1) | ~l1_pre_topc(X15)) )),
% 0.21/0.45    inference(superposition,[],[f76,f121])).
% 0.21/0.45  fof(f76,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X1] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f51])).
% 0.21/0.45  fof(f51,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),X0) & v4_pre_topc(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f49,f50])).
% 0.21/0.45  fof(f50,plain,(
% 0.21/0.45    ! [X2,X1,X0] : (? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),X0) & v4_pre_topc(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f49,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(rectify,[],[f48])).
% 0.21/0.45  fof(f48,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(nnf_transformation,[],[f25])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(flattening,[],[f24])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f12])).
% 0.21/0.45  fof(f12,axiom,(
% 0.21/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X3,X1) => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)))))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_pre_topc)).
% 0.21/0.45  fof(f731,plain,(
% 0.21/0.45    v4_pre_topc(k9_relat_1(sK2,sK4(sK0,sK1,sK2)),sK1) | ~spl5_14),
% 0.21/0.45    inference(avatar_component_clause,[],[f729])).
% 0.21/0.45  fof(f729,plain,(
% 0.21/0.45    spl5_14 <=> v4_pre_topc(k9_relat_1(sK2,sK4(sK0,sK1,sK2)),sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.45  fof(f131,plain,(
% 0.21/0.45    ( ! [X0] : (m1_subset_1(k9_relat_1(sK2,X0),k1_zfmisc_1(k2_relat_1(sK2)))) )),
% 0.21/0.45    inference(backward_demodulation,[],[f120,f121])).
% 0.21/0.45  fof(f120,plain,(
% 0.21/0.45    ( ! [X0] : (m1_subset_1(k9_relat_1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.21/0.45    inference(forward_demodulation,[],[f116,f118])).
% 0.21/0.45  fof(f118,plain,(
% 0.21/0.45    ( ! [X0] : (k9_relat_1(sK2,X0) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) )),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f66,f102])).
% 0.21/0.45  fof(f102,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f43])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(ennf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.45  fof(f116,plain,(
% 0.21/0.45    ( ! [X0] : (m1_subset_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f66,f100])).
% 0.21/0.45  fof(f100,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f41])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(ennf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 0.21/0.45  fof(f72,plain,(
% 0.21/0.45    v5_pre_topc(sK2,sK0,sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f47])).
% 0.21/0.45  fof(f726,plain,(
% 0.21/0.45    ~v4_pre_topc(sK4(sK0,sK1,sK2),sK0) | spl5_13),
% 0.21/0.45    inference(avatar_component_clause,[],[f725])).
% 0.21/0.45  fof(f725,plain,(
% 0.21/0.45    spl5_13 <=> v4_pre_topc(sK4(sK0,sK1,sK2),sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.45  fof(f764,plain,(
% 0.21/0.45    ~spl5_13),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f762])).
% 0.21/0.45  fof(f762,plain,(
% 0.21/0.45    $false | ~spl5_13),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f727,f690,f757,f682])).
% 0.21/0.45  fof(f682,plain,(
% 0.21/0.45    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_relat_1(sK2))) | v4_pre_topc(k9_relat_1(sK2,X2),sK1) | ~v4_pre_topc(X2,sK0)) )),
% 0.21/0.45    inference(global_subsumption,[],[f72,f64,f136,f137,f681])).
% 0.21/0.45  fof(f681,plain,(
% 0.21/0.45    ( ! [X2] : (v4_pre_topc(k9_relat_1(sK2,X2),sK1) | ~v4_pre_topc(X2,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_relat_1(sK2))) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))) )),
% 0.21/0.45    inference(forward_demodulation,[],[f680,f140])).
% 0.21/0.45  fof(f140,plain,(
% 0.21/0.45    ( ! [X0] : (k9_relat_1(sK2,X0) = k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,X0)) )),
% 0.21/0.45    inference(backward_demodulation,[],[f129,f133])).
% 0.21/0.45  fof(f129,plain,(
% 0.21/0.45    ( ! [X0] : (k9_relat_1(sK2,X0) = k7_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2,X0)) )),
% 0.21/0.45    inference(backward_demodulation,[],[f118,f121])).
% 0.21/0.45  fof(f680,plain,(
% 0.21/0.45    ( ! [X2] : (~v4_pre_topc(X2,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | v4_pre_topc(k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,X2),sK1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_relat_1(sK2))) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))) )),
% 0.21/0.45    inference(trivial_inequality_removal,[],[f679])).
% 0.21/0.45  fof(f679,plain,(
% 0.21/0.45    ( ! [X2] : (k2_relat_1(sK2) != k2_relat_1(sK2) | ~v4_pre_topc(X2,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | v4_pre_topc(k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,X2),sK1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_relat_1(sK2))) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))) )),
% 0.21/0.45    inference(superposition,[],[f675,f138])).
% 0.21/0.45  fof(f675,plain,(
% 0.21/0.45    ( ! [X2,X3] : (k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X2) | ~v4_pre_topc(X3,sK0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | v4_pre_topc(k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X2,X3),sK1) | ~m1_subset_1(X3,k1_zfmisc_1(k1_relat_1(sK2))) | ~v5_pre_topc(X2,sK0,sK1) | ~v1_funct_2(X2,k1_relat_1(sK2),k2_relat_1(sK2))) )),
% 0.21/0.45    inference(global_subsumption,[],[f67,f60,f59,f672])).
% 0.21/0.45  fof(f672,plain,(
% 0.21/0.45    ( ! [X2,X3] : (k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X2) | v4_pre_topc(k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X2,X3),sK1) | ~v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v5_pre_topc(X2,sK0,sK1) | ~v1_funct_2(X2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(X2) | ~v2_pre_topc(sK0) | ~v4_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(k1_relat_1(sK2)))) )),
% 0.21/0.45    inference(superposition,[],[f280,f133])).
% 0.21/0.45  fof(f280,plain,(
% 0.21/0.45    ( ! [X187,X188,X186] : (k2_relat_1(sK2) != k2_relset_1(u1_struct_0(X186),k2_relat_1(sK2),X187) | v4_pre_topc(k7_relset_1(u1_struct_0(X186),k2_relat_1(sK2),X187,X188),sK1) | ~v1_compts_1(X186) | ~l1_pre_topc(X186) | ~m1_subset_1(X187,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X186),k2_relat_1(sK2)))) | ~v5_pre_topc(X187,X186,sK1) | ~v1_funct_2(X187,u1_struct_0(X186),k2_relat_1(sK2)) | ~v1_funct_1(X187) | ~v2_pre_topc(X186) | ~v4_pre_topc(X188,X186) | ~m1_subset_1(X188,k1_zfmisc_1(u1_struct_0(X186)))) )),
% 0.21/0.45    inference(global_subsumption,[],[f68,f63,f62,f61,f279])).
% 0.21/0.45  fof(f279,plain,(
% 0.21/0.45    ( ! [X187,X188,X186] : (k2_relat_1(sK2) != k2_relset_1(u1_struct_0(X186),k2_relat_1(sK2),X187) | v4_pre_topc(k7_relset_1(u1_struct_0(X186),k2_relat_1(sK2),X187,X188),sK1) | ~v4_pre_topc(X188,X186) | ~m1_subset_1(X188,k1_zfmisc_1(u1_struct_0(X186))) | ~v5_pre_topc(X187,X186,sK1) | ~v8_pre_topc(sK1) | ~v1_compts_1(X186) | ~m1_subset_1(X187,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X186),k2_relat_1(sK2)))) | ~v1_funct_2(X187,u1_struct_0(X186),k2_relat_1(sK2)) | ~v1_funct_1(X187) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X186) | ~v2_pre_topc(X186)) )),
% 0.21/0.45    inference(forward_demodulation,[],[f233,f125])).
% 0.21/0.45  fof(f233,plain,(
% 0.21/0.45    ( ! [X187,X188,X186] : (v4_pre_topc(k7_relset_1(u1_struct_0(X186),k2_relat_1(sK2),X187,X188),sK1) | ~v4_pre_topc(X188,X186) | ~m1_subset_1(X188,k1_zfmisc_1(u1_struct_0(X186))) | ~v5_pre_topc(X187,X186,sK1) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X186),k2_relat_1(sK2),X187) | ~v8_pre_topc(sK1) | ~v1_compts_1(X186) | ~m1_subset_1(X187,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X186),k2_relat_1(sK2)))) | ~v1_funct_2(X187,u1_struct_0(X186),k2_relat_1(sK2)) | ~v1_funct_1(X187) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X186) | ~v2_pre_topc(X186)) )),
% 0.21/0.45    inference(superposition,[],[f88,f121])).
% 0.21/0.45  fof(f88,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v5_pre_topc(X2,X0,X1) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~v8_pre_topc(X1) | ~v1_compts_1(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v5_pre_topc(X2,X0,X1) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~v8_pre_topc(X1) | ~v1_compts_1(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.46    inference(flattening,[],[f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) | ~v4_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | (~v5_pre_topc(X2,X0,X1) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~v8_pre_topc(X1) | ~v1_compts_1(X0))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f16])).
% 0.21/0.46  fof(f16,axiom,(
% 0.21/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v5_pre_topc(X2,X0,X1) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & v8_pre_topc(X1) & v1_compts_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X3,X0) => v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)))))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_compts_1)).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    v2_pre_topc(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f47])).
% 0.21/0.46  fof(f68,plain,(
% 0.21/0.46    v8_pre_topc(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f47])).
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    v2_pre_topc(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f47])).
% 0.21/0.46  fof(f67,plain,(
% 0.21/0.46    v1_compts_1(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f47])).
% 0.21/0.46  fof(f757,plain,(
% 0.21/0.46    ~v4_pre_topc(k9_relat_1(sK2,sK4(sK0,sK1,sK2)),sK1) | ~spl5_13),
% 0.21/0.46    inference(forward_demodulation,[],[f751,f140])).
% 0.21/0.46  fof(f751,plain,(
% 0.21/0.46    ~v4_pre_topc(k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK4(sK0,sK1,sK2)),sK1) | ~spl5_13),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f64,f71,f73,f727,f136,f137,f142,f138,f748])).
% 0.21/0.46  fof(f748,plain,(
% 0.21/0.46    ( ! [X1] : (k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X1) | ~v4_pre_topc(k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X1,sK4(sK0,sK1,X1)),sK1) | ~v1_funct_1(X1) | v3_tops_2(X1,sK0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(X1,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v2_funct_1(X1) | ~v4_pre_topc(sK4(sK0,sK1,X1),sK0) | k1_relat_1(sK2) != k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X1)) )),
% 0.21/0.46    inference(global_subsumption,[],[f60,f747])).
% 0.21/0.46  fof(f747,plain,(
% 0.21/0.46    ( ! [X1] : (k1_relat_1(sK2) != k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X1) | ~v1_funct_1(X1) | ~v2_funct_1(X1) | ~v1_funct_2(X1,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v4_pre_topc(sK4(sK0,sK1,X1),sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | v3_tops_2(X1,sK0,sK1) | ~v4_pre_topc(k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X1,sK4(sK0,sK1,X1)),sK1) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X1)) )),
% 0.21/0.46    inference(forward_demodulation,[],[f742,f134])).
% 0.21/0.46  fof(f742,plain,(
% 0.21/0.46    ( ! [X1] : (k2_struct_0(sK0) != k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X1) | ~v1_funct_1(X1) | ~v2_funct_1(X1) | ~v1_funct_2(X1,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v4_pre_topc(sK4(sK0,sK1,X1),sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | v3_tops_2(X1,sK0,sK1) | ~v4_pre_topc(k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X1,sK4(sK0,sK1,X1)),sK1) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X1)) )),
% 0.21/0.46    inference(superposition,[],[f269,f133])).
% 0.21/0.46  fof(f269,plain,(
% 0.21/0.46    ( ! [X182,X181] : (k2_struct_0(X181) != k1_relset_1(u1_struct_0(X181),k2_relat_1(sK2),X182) | ~v1_funct_1(X182) | ~v2_funct_1(X182) | ~v1_funct_2(X182,u1_struct_0(X181),k2_relat_1(sK2)) | ~v4_pre_topc(sK4(X181,sK1,X182),X181) | ~l1_pre_topc(X181) | ~m1_subset_1(X182,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X181),k2_relat_1(sK2)))) | v3_tops_2(X182,X181,sK1) | ~v4_pre_topc(k7_relset_1(u1_struct_0(X181),k2_relat_1(sK2),X182,sK4(X181,sK1,X182)),sK1) | k2_relat_1(sK2) != k2_relset_1(u1_struct_0(X181),k2_relat_1(sK2),X182)) )),
% 0.21/0.46    inference(global_subsumption,[],[f63,f61,f268])).
% 0.21/0.46  fof(f268,plain,(
% 0.21/0.46    ( ! [X182,X181] : (k2_relat_1(sK2) != k2_relset_1(u1_struct_0(X181),k2_relat_1(sK2),X182) | ~v4_pre_topc(k7_relset_1(u1_struct_0(X181),k2_relat_1(sK2),X182,sK4(X181,sK1,X182)),sK1) | v3_tops_2(X182,X181,sK1) | ~v4_pre_topc(sK4(X181,sK1,X182),X181) | ~v2_funct_1(X182) | k2_struct_0(X181) != k1_relset_1(u1_struct_0(X181),k2_relat_1(sK2),X182) | ~m1_subset_1(X182,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X181),k2_relat_1(sK2)))) | ~v1_funct_2(X182,u1_struct_0(X181),k2_relat_1(sK2)) | ~v1_funct_1(X182) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X181)) )),
% 0.21/0.46    inference(forward_demodulation,[],[f231,f125])).
% 0.21/0.46  fof(f231,plain,(
% 0.21/0.46    ( ! [X182,X181] : (~v4_pre_topc(k7_relset_1(u1_struct_0(X181),k2_relat_1(sK2),X182,sK4(X181,sK1,X182)),sK1) | v3_tops_2(X182,X181,sK1) | ~v4_pre_topc(sK4(X181,sK1,X182),X181) | ~v2_funct_1(X182) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X181),k2_relat_1(sK2),X182) | k2_struct_0(X181) != k1_relset_1(u1_struct_0(X181),k2_relat_1(sK2),X182) | ~m1_subset_1(X182,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X181),k2_relat_1(sK2)))) | ~v1_funct_2(X182,u1_struct_0(X181),k2_relat_1(sK2)) | ~v1_funct_1(X182) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X181)) )),
% 0.21/0.46    inference(superposition,[],[f87,f121])).
% 0.21/0.46  fof(f87,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (v3_tops_2(X2,X0,X1) | ~v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X1) | ~v4_pre_topc(sK4(X0,X1,X2),X0) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f56])).
% 0.21/0.46  fof(f727,plain,(
% 0.21/0.46    v4_pre_topc(sK4(sK0,sK1,sK2),sK0) | ~spl5_13),
% 0.21/0.46    inference(avatar_component_clause,[],[f725])).
% 0.21/0.46  fof(f732,plain,(
% 0.21/0.46    spl5_13 | spl5_14),
% 0.21/0.46    inference(avatar_split_clause,[],[f723,f729,f725])).
% 0.21/0.46  fof(f723,plain,(
% 0.21/0.46    v4_pre_topc(k9_relat_1(sK2,sK4(sK0,sK1,sK2)),sK1) | v4_pre_topc(sK4(sK0,sK1,sK2),sK0)),
% 0.21/0.46    inference(global_subsumption,[],[f73,f71,f64,f136,f137,f722])).
% 0.21/0.46  fof(f722,plain,(
% 0.21/0.46    v4_pre_topc(k9_relat_1(sK2,sK4(sK0,sK1,sK2)),sK1) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | v3_tops_2(sK2,sK0,sK1) | v4_pre_topc(sK4(sK0,sK1,sK2),sK0)),
% 0.21/0.46    inference(forward_demodulation,[],[f721,f140])).
% 0.21/0.46  fof(f721,plain,(
% 0.21/0.46    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | v4_pre_topc(k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK4(sK0,sK1,sK2)),sK1) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | v3_tops_2(sK2,sK0,sK1) | v4_pre_topc(sK4(sK0,sK1,sK2),sK0)),
% 0.21/0.46    inference(trivial_inequality_removal,[],[f720])).
% 0.21/0.46  fof(f720,plain,(
% 0.21/0.46    k1_relat_1(sK2) != k1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | v4_pre_topc(k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK4(sK0,sK1,sK2)),sK1) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | v3_tops_2(sK2,sK0,sK1) | v4_pre_topc(sK4(sK0,sK1,sK2),sK0)),
% 0.21/0.46    inference(forward_demodulation,[],[f719,f142])).
% 0.21/0.46  fof(f719,plain,(
% 0.21/0.46    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | k1_relat_1(sK2) != k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | v4_pre_topc(k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK4(sK0,sK1,sK2)),sK1) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | v3_tops_2(sK2,sK0,sK1) | v4_pre_topc(sK4(sK0,sK1,sK2),sK0)),
% 0.21/0.46    inference(trivial_inequality_removal,[],[f718])).
% 0.21/0.46  fof(f718,plain,(
% 0.21/0.46    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | k1_relat_1(sK2) != k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | v4_pre_topc(k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK4(sK0,sK1,sK2)),sK1) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | v3_tops_2(sK2,sK0,sK1) | v4_pre_topc(sK4(sK0,sK1,sK2),sK0)),
% 0.21/0.46    inference(superposition,[],[f712,f138])).
% 0.21/0.46  fof(f712,plain,(
% 0.21/0.46    ( ! [X1] : (k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X1) | ~v1_funct_1(X1) | ~v2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | k1_relat_1(sK2) != k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X1) | v4_pre_topc(k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X1,sK4(sK0,sK1,X1)),sK1) | ~v1_funct_2(X1,k1_relat_1(sK2),k2_relat_1(sK2)) | v3_tops_2(X1,sK0,sK1) | v4_pre_topc(sK4(sK0,sK1,X1),sK0)) )),
% 0.21/0.46    inference(global_subsumption,[],[f60,f711])).
% 0.21/0.46  fof(f711,plain,(
% 0.21/0.46    ( ! [X1] : (k1_relat_1(sK2) != k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X1) | v4_pre_topc(sK4(sK0,sK1,X1),sK0) | v3_tops_2(X1,sK0,sK1) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X1) | v4_pre_topc(k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X1,sK4(sK0,sK1,X1)),sK1) | ~v1_funct_2(X1,k1_relat_1(sK2),k2_relat_1(sK2))) )),
% 0.21/0.46    inference(forward_demodulation,[],[f706,f134])).
% 0.21/0.46  fof(f706,plain,(
% 0.21/0.46    ( ! [X1] : (k2_struct_0(sK0) != k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X1) | v4_pre_topc(sK4(sK0,sK1,X1),sK0) | v3_tops_2(X1,sK0,sK1) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X1) | v4_pre_topc(k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X1,sK4(sK0,sK1,X1)),sK1) | ~v1_funct_2(X1,k1_relat_1(sK2),k2_relat_1(sK2))) )),
% 0.21/0.46    inference(superposition,[],[f265,f133])).
% 0.21/0.46  fof(f265,plain,(
% 0.21/0.46    ( ! [X161,X162] : (k2_struct_0(X161) != k1_relset_1(u1_struct_0(X161),k2_relat_1(sK2),X162) | v4_pre_topc(sK4(X161,sK1,X162),X161) | v3_tops_2(X162,X161,sK1) | ~v2_funct_1(X162) | ~v1_funct_1(X162) | ~l1_pre_topc(X161) | ~m1_subset_1(X162,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X161),k2_relat_1(sK2)))) | k2_relat_1(sK2) != k2_relset_1(u1_struct_0(X161),k2_relat_1(sK2),X162) | v4_pre_topc(k7_relset_1(u1_struct_0(X161),k2_relat_1(sK2),X162,sK4(X161,sK1,X162)),sK1) | ~v1_funct_2(X162,u1_struct_0(X161),k2_relat_1(sK2))) )),
% 0.21/0.46    inference(global_subsumption,[],[f63,f61,f264])).
% 0.21/0.46  fof(f264,plain,(
% 0.21/0.46    ( ! [X161,X162] : (k2_relat_1(sK2) != k2_relset_1(u1_struct_0(X161),k2_relat_1(sK2),X162) | v4_pre_topc(k7_relset_1(u1_struct_0(X161),k2_relat_1(sK2),X162,sK4(X161,sK1,X162)),sK1) | v3_tops_2(X162,X161,sK1) | v4_pre_topc(sK4(X161,sK1,X162),X161) | ~v2_funct_1(X162) | k2_struct_0(X161) != k1_relset_1(u1_struct_0(X161),k2_relat_1(sK2),X162) | ~m1_subset_1(X162,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X161),k2_relat_1(sK2)))) | ~v1_funct_2(X162,u1_struct_0(X161),k2_relat_1(sK2)) | ~v1_funct_1(X162) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X161)) )),
% 0.21/0.46    inference(forward_demodulation,[],[f221,f125])).
% 0.21/0.46  fof(f221,plain,(
% 0.21/0.46    ( ! [X161,X162] : (v4_pre_topc(k7_relset_1(u1_struct_0(X161),k2_relat_1(sK2),X162,sK4(X161,sK1,X162)),sK1) | v3_tops_2(X162,X161,sK1) | v4_pre_topc(sK4(X161,sK1,X162),X161) | ~v2_funct_1(X162) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X161),k2_relat_1(sK2),X162) | k2_struct_0(X161) != k1_relset_1(u1_struct_0(X161),k2_relat_1(sK2),X162) | ~m1_subset_1(X162,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X161),k2_relat_1(sK2)))) | ~v1_funct_2(X162,u1_struct_0(X161),k2_relat_1(sK2)) | ~v1_funct_1(X162) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X161)) )),
% 0.21/0.46    inference(superposition,[],[f86,f121])).
% 0.21/0.46  fof(f86,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (v3_tops_2(X2,X0,X1) | v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X1) | v4_pre_topc(sK4(X0,X1,X2),X0) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f56])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (24633)------------------------------
% 0.21/0.46  % (24633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (24633)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (24633)Memory used [KB]: 11897
% 0.21/0.46  % (24633)Time elapsed: 0.046 s
% 0.21/0.46  % (24633)------------------------------
% 0.21/0.46  % (24633)------------------------------
% 0.21/0.46  % (24617)Success in time 0.104 s
%------------------------------------------------------------------------------
