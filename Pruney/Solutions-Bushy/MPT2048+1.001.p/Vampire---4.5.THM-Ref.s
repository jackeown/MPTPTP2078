%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2048+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 146 expanded)
%              Number of leaves         :    9 (  53 expanded)
%              Depth                    :   15
%              Number of atoms          :  235 ( 835 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f198,plain,(
    $false ),
    inference(subsumption_resolution,[],[f197,f147])).

fof(f147,plain,(
    m1_subset_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f133,f28])).

fof(f28,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))),sK0,sK1)
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_waybel_0(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f21,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))),X0,X1)
                & m1_subset_1(X2,u1_struct_0(X1)) )
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(sK0,X1,X2)),u1_struct_0(sK0),u1_waybel_0(sK0,k4_waybel_9(sK0,X1,X2))),sK0,X1)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(sK0,X1,X2)),u1_struct_0(sK0),u1_waybel_0(sK0,k4_waybel_9(sK0,X1,X2))),sK0,X1)
            & m1_subset_1(X2,u1_struct_0(X1)) )
        & l1_waybel_0(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(sK0,sK1,X2)),u1_struct_0(sK0),u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,X2))),sK0,sK1)
          & m1_subset_1(X2,u1_struct_0(sK1)) )
      & l1_waybel_0(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X2] :
        ( ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(sK0,sK1,X2)),u1_struct_0(sK0),u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,X2))),sK0,sK1)
        & m1_subset_1(X2,u1_struct_0(sK1)) )
   => ( ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))),sK0,sK1)
      & m1_subset_1(sK2,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))),X0,X1)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))),X0,X1)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))),X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))),X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow19)).

fof(f133,plain,
    ( m1_subset_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0))))
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f129,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_waybel_0)).

fof(f129,plain,(
    l1_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0) ),
    inference(resolution,[],[f114,f31])).

fof(f31,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f114,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | l1_waybel_0(k4_waybel_9(sK0,sK1,X0),sK0) ) ),
    inference(subsumption_resolution,[],[f113,f27])).

fof(f27,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f113,plain,(
    ! [X0] :
      ( l1_waybel_0(k4_waybel_9(sK0,sK1,X0),sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f112,f28])).

fof(f112,plain,(
    ! [X0] :
      ( l1_waybel_0(k4_waybel_9(sK0,sK1,X0),sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f107,f29])).

fof(f29,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f107,plain,(
    ! [X0] :
      ( l1_waybel_0(k4_waybel_9(sK0,sK1,X0),sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f30,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_9)).

fof(f30,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f197,plain,(
    ~ m1_subset_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f171,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

% (18820)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f171,plain,(
    ~ m1_subset_1(k2_relset_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f170,f27])).

fof(f170,plain,
    ( ~ m1_subset_1(k2_relset_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f169,f28])).

fof(f169,plain,
    ( ~ m1_subset_1(k2_relset_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f168,f29])).

fof(f168,plain,
    ( ~ m1_subset_1(k2_relset_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f167,f30])).

fof(f167,plain,
    ( ~ m1_subset_1(k2_relset_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f166,f31])).

fof(f166,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(k2_relset_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f32,f39])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))),X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_yellow19(X2,X0,X1)
      | k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) != X2
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_yellow19(X2,X0,X1)
                  | ! [X3] :
                      ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) != X2
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,sK3(X0,X1,X2))),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,sK3(X0,X1,X2)))) = X2
                    & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) )
                  | ~ m1_yellow19(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X4)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X4))) = X2
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,sK3(X0,X1,X2))),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,sK3(X0,X1,X2)))) = X2
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_yellow19(X2,X0,X1)
                  | ! [X3] :
                      ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) != X2
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ? [X4] :
                      ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X4)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X4))) = X2
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_yellow19(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_yellow19(X2,X0,X1)
                  | ! [X3] :
                      ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) != X2
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ? [X3] :
                      ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) = X2
                      & m1_subset_1(X3,u1_struct_0(X1)) )
                  | ~ m1_yellow19(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_yellow19(X2,X0,X1)
              <=> ? [X3] :
                    ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) = X2
                    & m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_yellow19(X2,X0,X1)
              <=> ? [X3] :
                    ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) = X2
                    & m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_yellow19(X2,X0,X1)
              <=> ? [X3] :
                    ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) = X2
                    & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow19)).

fof(f32,plain,(
    ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))),sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

%------------------------------------------------------------------------------
