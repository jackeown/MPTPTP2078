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
% DateTime   : Thu Dec  3 13:19:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  259 (14221 expanded)
%              Number of leaves         :   31 (3777 expanded)
%              Depth                    :   40
%              Number of atoms          : 1348 (178553 expanded)
%              Number of equality atoms :  112 (2637 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f864,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f140,f144,f172,f195,f198,f246,f338,f464,f467,f471,f476,f804,f810,f819,f825,f863])).

fof(f863,plain,(
    spl5_9 ),
    inference(avatar_contradiction_clause,[],[f862])).

fof(f862,plain,
    ( $false
    | spl5_9 ),
    inference(subsumption_resolution,[],[f504,f860])).

fof(f860,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | spl5_9 ),
    inference(forward_demodulation,[],[f859,f285])).

fof(f285,plain,(
    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f237,f212])).

fof(f212,plain,(
    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f211,f62])).

fof(f62,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ( ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
      | ~ v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1))
      | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
      | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
      | ~ m1_pre_topc(sK1,sK0)
      | ~ v1_tsep_1(sK1,sK0) )
    & ( ( m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
        & v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1))
        & v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
        & v1_funct_1(k9_tmap_1(sK0,sK1)) )
      | ( m1_pre_topc(sK1,sK0)
        & v1_tsep_1(sK1,sK0) ) )
    & m1_pre_topc(sK1,sK0)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f43,f45,f44])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
              | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(k9_tmap_1(X0,X1))
              | ~ m1_pre_topc(X1,X0)
              | ~ v1_tsep_1(X1,X0) )
            & ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
                & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
                & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
                & v1_funct_1(k9_tmap_1(X0,X1)) )
              | ( m1_pre_topc(X1,X0)
                & v1_tsep_1(X1,X0) ) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(k9_tmap_1(sK0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X1)))))
            | ~ v5_pre_topc(k9_tmap_1(sK0,X1),sK0,k8_tmap_1(sK0,X1))
            | ~ v1_funct_2(k9_tmap_1(sK0,X1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X1)))
            | ~ v1_funct_1(k9_tmap_1(sK0,X1))
            | ~ m1_pre_topc(X1,sK0)
            | ~ v1_tsep_1(X1,sK0) )
          & ( ( m1_subset_1(k9_tmap_1(sK0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X1)))))
              & v5_pre_topc(k9_tmap_1(sK0,X1),sK0,k8_tmap_1(sK0,X1))
              & v1_funct_2(k9_tmap_1(sK0,X1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X1)))
              & v1_funct_1(k9_tmap_1(sK0,X1)) )
            | ( m1_pre_topc(X1,sK0)
              & v1_tsep_1(X1,sK0) ) )
          & m1_pre_topc(X1,sK0) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X1] :
        ( ( ~ m1_subset_1(k9_tmap_1(sK0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X1)))))
          | ~ v5_pre_topc(k9_tmap_1(sK0,X1),sK0,k8_tmap_1(sK0,X1))
          | ~ v1_funct_2(k9_tmap_1(sK0,X1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X1)))
          | ~ v1_funct_1(k9_tmap_1(sK0,X1))
          | ~ m1_pre_topc(X1,sK0)
          | ~ v1_tsep_1(X1,sK0) )
        & ( ( m1_subset_1(k9_tmap_1(sK0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X1)))))
            & v5_pre_topc(k9_tmap_1(sK0,X1),sK0,k8_tmap_1(sK0,X1))
            & v1_funct_2(k9_tmap_1(sK0,X1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X1)))
            & v1_funct_1(k9_tmap_1(sK0,X1)) )
          | ( m1_pre_topc(X1,sK0)
            & v1_tsep_1(X1,sK0) ) )
        & m1_pre_topc(X1,sK0) )
   => ( ( ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
        | ~ v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1))
        | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
        | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
        | ~ m1_pre_topc(sK1,sK0)
        | ~ v1_tsep_1(sK1,sK0) )
      & ( ( m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
          & v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1))
          & v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
          & v1_funct_1(k9_tmap_1(sK0,sK1)) )
        | ( m1_pre_topc(sK1,sK0)
          & v1_tsep_1(sK1,sK0) ) )
      & m1_pre_topc(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

% (14473)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
            | ~ v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
            | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
            | ~ v1_funct_1(k9_tmap_1(X0,X1))
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
              & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              & v1_funct_1(k9_tmap_1(X0,X1)) )
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
            | ~ v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
            | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
            | ~ v1_funct_1(k9_tmap_1(X0,X1))
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
              & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              & v1_funct_1(k9_tmap_1(X0,X1)) )
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
              & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              & v1_funct_1(k9_tmap_1(X0,X1)) ) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
              & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              & v1_funct_1(k9_tmap_1(X0,X1)) ) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ( ( m1_pre_topc(X1,X0)
                & v1_tsep_1(X1,X0) )
            <=> ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
                & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
                & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
                & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <=> ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
              & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t122_tmap_1)).

fof(f211,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f210,f63])).

fof(f63,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f210,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f209,f64])).

fof(f64,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f209,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f208,f65])).

fof(f65,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f208,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f207,f181])).

fof(f181,plain,(
    v1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f180,f62])).

fof(f180,plain,
    ( v1_pre_topc(k8_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f179,f63])).

fof(f179,plain,
    ( v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f155,f64])).

fof(f155,plain,
    ( v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f65,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).

fof(f207,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f206,f184])).

fof(f184,plain,(
    v2_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f183,f62])).

fof(f183,plain,
    ( v2_pre_topc(k8_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f182,f63])).

fof(f182,plain,
    ( v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f156,f64])).

fof(f156,plain,
    ( v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f65,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f206,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f199,f187])).

fof(f187,plain,(
    l1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f186,f62])).

fof(f186,plain,
    ( l1_pre_topc(k8_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f185,f63])).

fof(f185,plain,
    ( l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f157,f64])).

fof(f157,plain,
    ( l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f65,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f199,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f160,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( k6_tmap_1(X0,u1_struct_0(X1)) = X2
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( k6_tmap_1(X0,X4) = X2
      | u1_struct_0(X1) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ( k6_tmap_1(X0,sK3(X0,X1,X2)) != X2
                    & u1_struct_0(X1) = sK3(X0,X1,X2)
                    & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f52,f53])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK3(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK3(X0,X1,X2)
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f51])).

% (14479)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( k6_tmap_1(X0,X3) = X2
                      | u1_struct_0(X1) != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & v1_pre_topc(X2) )
             => ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => k6_tmap_1(X0,X3) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_tmap_1)).

fof(f160,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f150,f64])).

fof(f150,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f65,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f237,plain,(
    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f236,f62])).

fof(f236,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f235,f63])).

fof(f235,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f204,f64])).

fof(f204,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f160,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f859,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | spl5_9 ),
    inference(forward_demodulation,[],[f228,f212])).

fof(f228,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl5_9
  <=> m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f504,plain,(
    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f274,f285])).

fof(f274,plain,(
    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) ),
    inference(subsumption_resolution,[],[f273,f62])).

fof(f273,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f272,f63])).

fof(f272,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f271,f64])).

fof(f271,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f251,f160])).

fof(f251,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f106,f212])).

fof(f106,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(f825,plain,
    ( spl5_1
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(avatar_contradiction_clause,[],[f824])).

fof(f824,plain,
    ( $false
    | spl5_1
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f823,f64])).

fof(f823,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_1
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f822,f65])).

fof(f822,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl5_1
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f821,f119])).

fof(f119,plain,
    ( ~ v1_tsep_1(sK1,sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl5_1
  <=> v1_tsep_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f821,plain,
    ( v1_tsep_1(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f820,f232])).

fof(f232,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl5_10
  <=> v3_pre_topc(u1_struct_0(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f820,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | v1_tsep_1(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_8 ),
    inference(superposition,[],[f80,f171])).

fof(f171,plain,
    ( u1_struct_0(sK1) = sK2(sK0,sK1)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl5_8
  <=> u1_struct_0(sK1) = sK2(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(sK2(X0,X1),X0)
      | v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ( ~ v3_pre_topc(sK2(X0,X1),X0)
                & u1_struct_0(X1) = sK2(X0,X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f48,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK2(X0,X1),X0)
        & u1_struct_0(X1) = sK2(X0,X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_pre_topc(X2,X0)
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tsep_1)).

fof(f819,plain,
    ( ~ spl5_1
    | spl5_10 ),
    inference(avatar_split_clause,[],[f818,f231,f117])).

fof(f818,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f817,f64])).

fof(f817,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v1_tsep_1(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f200,f65])).

fof(f200,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v1_tsep_1(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f160,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(u1_struct_0(X1),X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f810,plain,
    ( ~ spl5_10
    | spl5_5
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_14
    | spl5_16 ),
    inference(avatar_split_clause,[],[f809,f357,f335,f227,f137,f129,f125,f133,f231])).

fof(f133,plain,
    ( spl5_5
  <=> v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f125,plain,
    ( spl5_3
  <=> v1_funct_1(k9_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f129,plain,
    ( spl5_4
  <=> v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f137,plain,
    ( spl5_6
  <=> m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f335,plain,
    ( spl5_14
  <=> r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f357,plain,
    ( spl5_16
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f809,plain,
    ( v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_14
    | spl5_16 ),
    inference(forward_demodulation,[],[f808,f712])).

fof(f712,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_14
    | spl5_16 ),
    inference(subsumption_resolution,[],[f711,f359])).

fof(f359,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl5_16 ),
    inference(avatar_component_clause,[],[f357])).

fof(f711,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f710,f126])).

fof(f126,plain,
    ( v1_funct_1(k9_tmap_1(sK0,sK1))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f125])).

fof(f710,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f709,f287])).

fof(f287,plain,
    ( v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl5_4 ),
    inference(backward_demodulation,[],[f130,f285])).

fof(f130,plain,
    ( v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f129])).

fof(f709,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f708,f473])).

fof(f473,plain,
    ( m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f138,f285])).

fof(f138,plain,
    ( m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f137])).

fof(f708,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_9
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f707,f218])).

fof(f218,plain,(
    v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f217,f62])).

fof(f217,plain,
    ( v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f216,f63])).

fof(f216,plain,
    ( v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f201,f64])).

fof(f201,plain,
    ( v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f160,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_funct_1(k7_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f707,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_9
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f706,f477])).

fof(f477,plain,(
    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f270,f285])).

fof(f270,plain,(
    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f269,f62])).

fof(f269,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f268,f63])).

fof(f268,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f267,f64])).

fof(f267,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f250,f160])).

fof(f250,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f105,f212])).

fof(f105,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f706,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_9
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f705,f503])).

fof(f503,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f502,f285])).

fof(f502,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f229,f212])).

fof(f229,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f227])).

fof(f705,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_14 ),
    inference(duplicate_literal_removal,[],[f704])).

fof(f704,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_14 ),
    inference(resolution,[],[f337,f107])).

fof(f107,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
      | X4 = X5
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
          | X4 != X5 )
        & ( X4 = X5
          | ~ r1_funct_2(X0,X1,X2,X3,X4,X5) ) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

fof(f337,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f335])).

fof(f808,plain,
    ( v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(u1_struct_0(sK1),sK0) ),
    inference(subsumption_resolution,[],[f807,f62])).

fof(f807,plain,
    ( v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f806,f63])).

fof(f806,plain,
    ( v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f805,f64])).

fof(f805,plain,
    ( v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f253,f160])).

fof(f253,plain,
    ( v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f94,f212])).

fof(f94,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
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
    inference(flattening,[],[f59])).

fof(f59,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_tmap_1)).

fof(f804,plain,
    ( spl5_10
    | ~ spl5_5
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_14
    | spl5_16 ),
    inference(avatar_split_clause,[],[f803,f357,f335,f227,f137,f129,f125,f133,f231])).

fof(f803,plain,
    ( ~ v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1))
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_14
    | spl5_16 ),
    inference(subsumption_resolution,[],[f802,f126])).

fof(f802,plain,
    ( ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | ~ v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1))
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_14
    | spl5_16 ),
    inference(forward_demodulation,[],[f801,f712])).

fof(f801,plain,
    ( ~ v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1))
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_14
    | spl5_16 ),
    inference(subsumption_resolution,[],[f800,f287])).

fof(f800,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1))
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_14
    | spl5_16 ),
    inference(forward_demodulation,[],[f799,f712])).

fof(f799,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1))
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_14
    | spl5_16 ),
    inference(forward_demodulation,[],[f798,f285])).

fof(f798,plain,
    ( ~ v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1))
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_14
    | spl5_16 ),
    inference(forward_demodulation,[],[f797,f712])).

fof(f797,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_14
    | spl5_16 ),
    inference(subsumption_resolution,[],[f796,f473])).

fof(f796,plain,
    ( ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_14
    | spl5_16 ),
    inference(forward_demodulation,[],[f795,f712])).

fof(f795,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f794,f285])).

fof(f794,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f793,f62])).

fof(f793,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f792,f63])).

fof(f792,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f791,f64])).

fof(f791,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f254,f160])).

fof(f254,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f96,f212])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | v3_pre_topc(X1,X0)
      | ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
      | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f476,plain,
    ( ~ spl5_6
    | spl5_13 ),
    inference(avatar_contradiction_clause,[],[f475])).

fof(f475,plain,
    ( $false
    | ~ spl5_6
    | spl5_13 ),
    inference(subsumption_resolution,[],[f333,f473])).

fof(f333,plain,
    ( ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | spl5_13 ),
    inference(avatar_component_clause,[],[f331])).

fof(f331,plain,
    ( spl5_13
  <=> m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f471,plain,(
    spl5_6 ),
    inference(avatar_contradiction_clause,[],[f470])).

fof(f470,plain,
    ( $false
    | spl5_6 ),
    inference(subsumption_resolution,[],[f469,f286])).

fof(f286,plain,
    ( ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | spl5_6 ),
    inference(backward_demodulation,[],[f139,f285])).

fof(f139,plain,
    ( ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f137])).

fof(f469,plain,(
    m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f193,f285])).

fof(f193,plain,(
    m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) ),
    inference(subsumption_resolution,[],[f192,f62])).

fof(f192,plain,
    ( m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f191,f63])).

fof(f191,plain,
    ( m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f159,f64])).

fof(f159,plain,
    ( m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f65,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_tmap_1)).

fof(f467,plain,
    ( ~ spl5_4
    | spl5_12 ),
    inference(avatar_contradiction_clause,[],[f466])).

fof(f466,plain,
    ( $false
    | ~ spl5_4
    | spl5_12 ),
    inference(subsumption_resolution,[],[f329,f287])).

fof(f329,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f327])).

fof(f327,plain,
    ( spl5_12
  <=> v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f464,plain,(
    ~ spl5_16 ),
    inference(avatar_contradiction_clause,[],[f463])).

fof(f463,plain,
    ( $false
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f462,f62])).

fof(f462,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f461,f149])).

fof(f149,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f64,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f461,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_16 ),
    inference(resolution,[],[f358,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f358,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f357])).

fof(f338,plain,
    ( ~ spl5_12
    | ~ spl5_13
    | spl5_14
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f325,f125,f335,f331,f327])).

fof(f325,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f324,f285])).

fof(f324,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f323,f212])).

fof(f323,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f322,f62])).

fof(f322,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f321,f63])).

fof(f321,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f320,f64])).

fof(f320,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f319,f65])).

fof(f319,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f318,f126])).

fof(f318,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f289,f160])).

fof(f289,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f113,f285])).

fof(f113,plain,(
    ! [X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),X2,k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k9_tmap_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4))
      | u1_struct_0(X1) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | k9_tmap_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK4(X0,X1,X2))),X2,k7_tmap_1(X0,sK4(X0,X1,X2)))
                    & u1_struct_0(X1) = sK4(X0,X1,X2)
                    & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4))
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f56,f57])).

fof(f57,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK4(X0,X1,X2))),X2,k7_tmap_1(X0,sK4(X0,X1,X2)))
        & u1_struct_0(X1) = sK4(X0,X1,X2)
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4))
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      | u1_struct_0(X1) != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
                & v1_funct_1(X2) )
             => ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_tmap_1)).

fof(f246,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f245])).

fof(f245,plain,
    ( $false
    | spl5_4 ),
    inference(subsumption_resolution,[],[f244,f62])).

fof(f244,plain,
    ( v2_struct_0(sK0)
    | spl5_4 ),
    inference(subsumption_resolution,[],[f243,f63])).

fof(f243,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_4 ),
    inference(subsumption_resolution,[],[f242,f64])).

fof(f242,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_4 ),
    inference(subsumption_resolution,[],[f241,f65])).

fof(f241,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_4 ),
    inference(resolution,[],[f131,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f131,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f129])).

fof(f198,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f197])).

fof(f197,plain,
    ( $false
    | spl5_3 ),
    inference(subsumption_resolution,[],[f190,f127])).

fof(f127,plain,
    ( ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f125])).

fof(f190,plain,(
    v1_funct_1(k9_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f189,f62])).

fof(f189,plain,
    ( v1_funct_1(k9_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f188,f63])).

fof(f188,plain,
    ( v1_funct_1(k9_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f158,f64])).

fof(f158,plain,
    ( v1_funct_1(k9_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f65,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v1_funct_1(k9_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f195,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f194])).

fof(f194,plain,
    ( $false
    | spl5_2 ),
    inference(subsumption_resolution,[],[f123,f65])).

fof(f123,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl5_2
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f172,plain,
    ( spl5_1
    | spl5_8 ),
    inference(avatar_split_clause,[],[f167,f169,f117])).

fof(f167,plain,
    ( u1_struct_0(sK1) = sK2(sK0,sK1)
    | v1_tsep_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f152,f64])).

fof(f152,plain,
    ( u1_struct_0(sK1) = sK2(sK0,sK1)
    | v1_tsep_1(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f65,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | u1_struct_0(X1) = sK2(X0,X1)
      | v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f144,plain,
    ( spl5_1
    | spl5_5 ),
    inference(avatar_split_clause,[],[f70,f133,f117])).

fof(f70,plain,
    ( v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1))
    | v1_tsep_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f140,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f74,f137,f133,f129,f125,f121,f117])).

fof(f74,plain,
    ( ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:33:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (14475)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.46  % (14483)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.48  % (14475)Refutation not found, incomplete strategy% (14475)------------------------------
% 0.21/0.48  % (14475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (14475)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (14475)Memory used [KB]: 1791
% 0.21/0.48  % (14475)Time elapsed: 0.078 s
% 0.21/0.48  % (14475)------------------------------
% 0.21/0.48  % (14475)------------------------------
% 0.21/0.49  % (14472)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.49  % (14468)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.49  % (14468)Refutation not found, incomplete strategy% (14468)------------------------------
% 0.21/0.49  % (14468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (14468)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (14468)Memory used [KB]: 10618
% 0.21/0.49  % (14468)Time elapsed: 0.083 s
% 0.21/0.49  % (14468)------------------------------
% 0.21/0.49  % (14468)------------------------------
% 0.21/0.50  % (14470)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (14490)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.50  % (14487)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.50  % (14489)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.50  % (14469)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (14484)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.51  % (14480)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (14478)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (14474)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (14485)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.51  % (14476)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (14477)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (14492)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (14493)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.52  % (14474)Refutation not found, incomplete strategy% (14474)------------------------------
% 0.21/0.52  % (14474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (14474)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (14474)Memory used [KB]: 10746
% 0.21/0.52  % (14474)Time elapsed: 0.101 s
% 0.21/0.52  % (14474)------------------------------
% 0.21/0.52  % (14474)------------------------------
% 0.21/0.53  % (14469)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f864,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f140,f144,f172,f195,f198,f246,f338,f464,f467,f471,f476,f804,f810,f819,f825,f863])).
% 0.21/0.53  fof(f863,plain,(
% 0.21/0.53    spl5_9),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f862])).
% 0.21/0.53  fof(f862,plain,(
% 0.21/0.53    $false | spl5_9),
% 0.21/0.53    inference(subsumption_resolution,[],[f504,f860])).
% 0.21/0.53  fof(f860,plain,(
% 0.21/0.53    ~m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | spl5_9),
% 0.21/0.53    inference(forward_demodulation,[],[f859,f285])).
% 0.21/0.53  fof(f285,plain,(
% 0.21/0.53    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))),
% 0.21/0.53    inference(forward_demodulation,[],[f237,f212])).
% 0.21/0.53  fof(f212,plain,(
% 0.21/0.53    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))),
% 0.21/0.53    inference(subsumption_resolution,[],[f211,f62])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ~v2_struct_0(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ((~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1)) | ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(k9_tmap_1(sK0,sK1)) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)) & ((m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) & v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1)) & v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) & v1_funct_1(k9_tmap_1(sK0,sK1))) | (m1_pre_topc(sK1,sK0) & v1_tsep_1(sK1,sK0))) & m1_pre_topc(sK1,sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f43,f45,f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~m1_subset_1(k9_tmap_1(sK0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X1))))) | ~v5_pre_topc(k9_tmap_1(sK0,X1),sK0,k8_tmap_1(sK0,X1)) | ~v1_funct_2(k9_tmap_1(sK0,X1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X1))) | ~v1_funct_1(k9_tmap_1(sK0,X1)) | ~m1_pre_topc(X1,sK0) | ~v1_tsep_1(X1,sK0)) & ((m1_subset_1(k9_tmap_1(sK0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X1))))) & v5_pre_topc(k9_tmap_1(sK0,X1),sK0,k8_tmap_1(sK0,X1)) & v1_funct_2(k9_tmap_1(sK0,X1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X1))) & v1_funct_1(k9_tmap_1(sK0,X1))) | (m1_pre_topc(X1,sK0) & v1_tsep_1(X1,sK0))) & m1_pre_topc(X1,sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ? [X1] : ((~m1_subset_1(k9_tmap_1(sK0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X1))))) | ~v5_pre_topc(k9_tmap_1(sK0,X1),sK0,k8_tmap_1(sK0,X1)) | ~v1_funct_2(k9_tmap_1(sK0,X1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X1))) | ~v1_funct_1(k9_tmap_1(sK0,X1)) | ~m1_pre_topc(X1,sK0) | ~v1_tsep_1(X1,sK0)) & ((m1_subset_1(k9_tmap_1(sK0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X1))))) & v5_pre_topc(k9_tmap_1(sK0,X1),sK0,k8_tmap_1(sK0,X1)) & v1_funct_2(k9_tmap_1(sK0,X1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X1))) & v1_funct_1(k9_tmap_1(sK0,X1))) | (m1_pre_topc(X1,sK0) & v1_tsep_1(X1,sK0))) & m1_pre_topc(X1,sK0)) => ((~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1)) | ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(k9_tmap_1(sK0,sK1)) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)) & ((m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) & v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1)) & v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) & v1_funct_1(k9_tmap_1(sK0,sK1))) | (m1_pre_topc(sK1,sK0) & v1_tsep_1(sK1,sK0))) & m1_pre_topc(sK1,sK0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  % (14473)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((((~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) & ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1)))) & m1_pre_topc(X1,X0)) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))))),
% 0.21/0.53    inference(negated_conjecture,[],[f14])).
% 0.21/0.53  fof(f14,conjecture,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t122_tmap_1)).
% 0.21/0.53  fof(f211,plain,(
% 0.21/0.53    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f210,f63])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    v2_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f46])).
% 0.21/0.53  fof(f210,plain,(
% 0.21/0.53    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f209,f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    l1_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f46])).
% 0.21/0.53  fof(f209,plain,(
% 0.21/0.53    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f208,f65])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    m1_pre_topc(sK1,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f46])).
% 0.21/0.53  fof(f208,plain,(
% 0.21/0.53    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f207,f181])).
% 0.21/0.53  fof(f181,plain,(
% 0.21/0.53    v1_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.21/0.53    inference(subsumption_resolution,[],[f180,f62])).
% 0.21/0.53  fof(f180,plain,(
% 0.21/0.53    v1_pre_topc(k8_tmap_1(sK0,sK1)) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f179,f63])).
% 0.21/0.53  fof(f179,plain,(
% 0.21/0.53    v1_pre_topc(k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f155,f64])).
% 0.21/0.53  fof(f155,plain,(
% 0.21/0.53    v1_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(resolution,[],[f65,f98])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v1_pre_topc(k8_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).
% 0.21/0.53  fof(f207,plain,(
% 0.21/0.53    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~v1_pre_topc(k8_tmap_1(sK0,sK1)) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f206,f184])).
% 0.21/0.53  fof(f184,plain,(
% 0.21/0.53    v2_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.21/0.53    inference(subsumption_resolution,[],[f183,f62])).
% 0.21/0.53  fof(f183,plain,(
% 0.21/0.53    v2_pre_topc(k8_tmap_1(sK0,sK1)) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f182,f63])).
% 0.21/0.53  fof(f182,plain,(
% 0.21/0.53    v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f156,f64])).
% 0.21/0.53  fof(f156,plain,(
% 0.21/0.53    v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(resolution,[],[f65,f99])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(k8_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f206,plain,(
% 0.21/0.53    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~v1_pre_topc(k8_tmap_1(sK0,sK1)) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f199,f187])).
% 0.21/0.53  fof(f187,plain,(
% 0.21/0.53    l1_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.21/0.53    inference(subsumption_resolution,[],[f186,f62])).
% 0.21/0.53  fof(f186,plain,(
% 0.21/0.53    l1_pre_topc(k8_tmap_1(sK0,sK1)) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f185,f63])).
% 0.21/0.53  fof(f185,plain,(
% 0.21/0.53    l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f157,f64])).
% 0.21/0.53  fof(f157,plain,(
% 0.21/0.53    l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(resolution,[],[f65,f100])).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(k8_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f199,plain,(
% 0.21/0.53    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~v1_pre_topc(k8_tmap_1(sK0,sK1)) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(resolution,[],[f160,f111])).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f110])).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k6_tmap_1(X0,u1_struct_0(X1)) = X2 | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f82])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X1] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | (k6_tmap_1(X0,sK3(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK3(X0,X1,X2) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f52,f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ! [X2,X1,X0] : (? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k6_tmap_1(X0,sK3(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK3(X0,X1,X2) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(rectify,[],[f51])).
% 0.21/0.53  % (14479)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_tmap_1)).
% 0.21/0.53  fof(f160,plain,(
% 0.21/0.53    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f150,f64])).
% 0.21/0.53  fof(f150,plain,(
% 0.21/0.53    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f65,f76])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.53  fof(f237,plain,(
% 0.21/0.53    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f236,f62])).
% 0.21/0.53  fof(f236,plain,(
% 0.21/0.53    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f235,f63])).
% 0.21/0.53  fof(f235,plain,(
% 0.21/0.53    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f204,f64])).
% 0.21/0.53  fof(f204,plain,(
% 0.21/0.53    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(resolution,[],[f160,f90])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).
% 0.21/0.53  fof(f859,plain,(
% 0.21/0.53    ~m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | spl5_9),
% 0.21/0.53    inference(forward_demodulation,[],[f228,f212])).
% 0.21/0.53  fof(f228,plain,(
% 0.21/0.53    ~m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))))) | spl5_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f227])).
% 0.21/0.53  fof(f227,plain,(
% 0.21/0.53    spl5_9 <=> m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.53  fof(f504,plain,(
% 0.21/0.53    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 0.21/0.53    inference(forward_demodulation,[],[f274,f285])).
% 0.21/0.53  fof(f274,plain,(
% 0.21/0.53    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))),
% 0.21/0.53    inference(subsumption_resolution,[],[f273,f62])).
% 0.21/0.53  fof(f273,plain,(
% 0.21/0.53    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f272,f63])).
% 0.21/0.53  fof(f272,plain,(
% 0.21/0.53    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f271,f64])).
% 0.21/0.53  fof(f271,plain,(
% 0.21/0.53    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f251,f160])).
% 0.21/0.53  fof(f251,plain,(
% 0.21/0.53    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(superposition,[],[f106,f212])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).
% 0.21/0.53  fof(f825,plain,(
% 0.21/0.53    spl5_1 | ~spl5_8 | ~spl5_10),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f824])).
% 0.21/0.53  fof(f824,plain,(
% 0.21/0.53    $false | (spl5_1 | ~spl5_8 | ~spl5_10)),
% 0.21/0.53    inference(subsumption_resolution,[],[f823,f64])).
% 0.21/0.53  fof(f823,plain,(
% 0.21/0.53    ~l1_pre_topc(sK0) | (spl5_1 | ~spl5_8 | ~spl5_10)),
% 0.21/0.53    inference(subsumption_resolution,[],[f822,f65])).
% 0.21/0.53  fof(f822,plain,(
% 0.21/0.53    ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | (spl5_1 | ~spl5_8 | ~spl5_10)),
% 0.21/0.53    inference(subsumption_resolution,[],[f821,f119])).
% 0.21/0.53  fof(f119,plain,(
% 0.21/0.53    ~v1_tsep_1(sK1,sK0) | spl5_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f117])).
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    spl5_1 <=> v1_tsep_1(sK1,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.53  fof(f821,plain,(
% 0.21/0.53    v1_tsep_1(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | (~spl5_8 | ~spl5_10)),
% 0.21/0.53    inference(subsumption_resolution,[],[f820,f232])).
% 0.21/0.53  fof(f232,plain,(
% 0.21/0.53    v3_pre_topc(u1_struct_0(sK1),sK0) | ~spl5_10),
% 0.21/0.53    inference(avatar_component_clause,[],[f231])).
% 0.21/0.53  fof(f231,plain,(
% 0.21/0.53    spl5_10 <=> v3_pre_topc(u1_struct_0(sK1),sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.53  fof(f820,plain,(
% 0.21/0.53    ~v3_pre_topc(u1_struct_0(sK1),sK0) | v1_tsep_1(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~spl5_8),
% 0.21/0.53    inference(superposition,[],[f80,f171])).
% 0.21/0.53  fof(f171,plain,(
% 0.21/0.53    u1_struct_0(sK1) = sK2(sK0,sK1) | ~spl5_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f169])).
% 0.21/0.53  fof(f169,plain,(
% 0.21/0.53    spl5_8 <=> u1_struct_0(sK1) = sK2(sK0,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v3_pre_topc(sK2(X0,X1),X0) | v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | (~v3_pre_topc(sK2(X0,X1),X0) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f48,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK2(X0,X1),X0) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(rectify,[],[f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tsep_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_pre_topc(X2,X0))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tsep_1)).
% 0.21/0.53  fof(f819,plain,(
% 0.21/0.53    ~spl5_1 | spl5_10),
% 0.21/0.53    inference(avatar_split_clause,[],[f818,f231,f117])).
% 0.21/0.53  fof(f818,plain,(
% 0.21/0.53    v3_pre_topc(u1_struct_0(sK1),sK0) | ~v1_tsep_1(sK1,sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f817,f64])).
% 0.21/0.53  fof(f817,plain,(
% 0.21/0.53    v3_pre_topc(u1_struct_0(sK1),sK0) | ~v1_tsep_1(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f200,f65])).
% 0.21/0.53  fof(f200,plain,(
% 0.21/0.53    v3_pre_topc(u1_struct_0(sK1),sK0) | ~v1_tsep_1(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f160,f109])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(u1_struct_0(X1),X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f77])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f50])).
% 0.21/0.53  fof(f810,plain,(
% 0.21/0.53    ~spl5_10 | spl5_5 | ~spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_9 | ~spl5_14 | spl5_16),
% 0.21/0.53    inference(avatar_split_clause,[],[f809,f357,f335,f227,f137,f129,f125,f133,f231])).
% 0.21/0.53  fof(f133,plain,(
% 0.21/0.53    spl5_5 <=> v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    spl5_3 <=> v1_funct_1(k9_tmap_1(sK0,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.53  fof(f129,plain,(
% 0.21/0.53    spl5_4 <=> v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.53  fof(f137,plain,(
% 0.21/0.53    spl5_6 <=> m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.53  fof(f335,plain,(
% 0.21/0.53    spl5_14 <=> r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.53  fof(f357,plain,(
% 0.21/0.53    spl5_16 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.53  fof(f809,plain,(
% 0.21/0.53    v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1)) | ~v3_pre_topc(u1_struct_0(sK1),sK0) | (~spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_9 | ~spl5_14 | spl5_16)),
% 0.21/0.53    inference(forward_demodulation,[],[f808,f712])).
% 0.21/0.53  fof(f712,plain,(
% 0.21/0.53    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | (~spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_9 | ~spl5_14 | spl5_16)),
% 0.21/0.53    inference(subsumption_resolution,[],[f711,f359])).
% 0.21/0.53  fof(f359,plain,(
% 0.21/0.53    ~v1_xboole_0(u1_struct_0(sK0)) | spl5_16),
% 0.21/0.53    inference(avatar_component_clause,[],[f357])).
% 0.21/0.53  fof(f711,plain,(
% 0.21/0.53    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK0)) | (~spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_9 | ~spl5_14)),
% 0.21/0.53    inference(subsumption_resolution,[],[f710,f126])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    v1_funct_1(k9_tmap_1(sK0,sK1)) | ~spl5_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f125])).
% 0.21/0.53  fof(f710,plain,(
% 0.21/0.53    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~v1_funct_1(k9_tmap_1(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK0)) | (~spl5_4 | ~spl5_6 | ~spl5_9 | ~spl5_14)),
% 0.21/0.53    inference(subsumption_resolution,[],[f709,f287])).
% 0.21/0.53  fof(f287,plain,(
% 0.21/0.53    v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~spl5_4),
% 0.21/0.53    inference(backward_demodulation,[],[f130,f285])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~spl5_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f129])).
% 0.21/0.53  fof(f709,plain,(
% 0.21/0.53    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k9_tmap_1(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK0)) | (~spl5_6 | ~spl5_9 | ~spl5_14)),
% 0.21/0.53    inference(subsumption_resolution,[],[f708,f473])).
% 0.21/0.53  fof(f473,plain,(
% 0.21/0.53    m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~spl5_6),
% 0.21/0.53    inference(forward_demodulation,[],[f138,f285])).
% 0.21/0.53  fof(f138,plain,(
% 0.21/0.53    m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~spl5_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f137])).
% 0.21/0.53  fof(f708,plain,(
% 0.21/0.53    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k9_tmap_1(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK0)) | (~spl5_9 | ~spl5_14)),
% 0.21/0.53    inference(subsumption_resolution,[],[f707,f218])).
% 0.21/0.53  fof(f218,plain,(
% 0.21/0.53    v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f217,f62])).
% 0.21/0.53  fof(f217,plain,(
% 0.21/0.53    v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f216,f63])).
% 0.21/0.53  fof(f216,plain,(
% 0.21/0.53    v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f201,f64])).
% 0.21/0.53  fof(f201,plain,(
% 0.21/0.53    v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(resolution,[],[f160,f104])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_funct_1(k7_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f707,plain,(
% 0.21/0.53    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k9_tmap_1(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK0)) | (~spl5_9 | ~spl5_14)),
% 0.21/0.53    inference(subsumption_resolution,[],[f706,f477])).
% 0.21/0.53  fof(f477,plain,(
% 0.21/0.53    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0))),
% 0.21/0.53    inference(forward_demodulation,[],[f270,f285])).
% 0.21/0.53  fof(f270,plain,(
% 0.21/0.53    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f269,f62])).
% 0.21/0.53  fof(f269,plain,(
% 0.21/0.53    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f268,f63])).
% 0.21/0.53  fof(f268,plain,(
% 0.21/0.53    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f267,f64])).
% 0.21/0.53  fof(f267,plain,(
% 0.21/0.53    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f250,f160])).
% 0.21/0.53  fof(f250,plain,(
% 0.21/0.53    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(superposition,[],[f105,f212])).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f706,plain,(
% 0.21/0.53    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k9_tmap_1(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK0)) | (~spl5_9 | ~spl5_14)),
% 0.21/0.53    inference(subsumption_resolution,[],[f705,f503])).
% 0.21/0.53  fof(f503,plain,(
% 0.21/0.53    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~spl5_9),
% 0.21/0.53    inference(forward_demodulation,[],[f502,f285])).
% 0.21/0.53  fof(f502,plain,(
% 0.21/0.53    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~spl5_9),
% 0.21/0.53    inference(forward_demodulation,[],[f229,f212])).
% 0.21/0.53  fof(f229,plain,(
% 0.21/0.53    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))))) | ~spl5_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f227])).
% 0.21/0.53  fof(f705,plain,(
% 0.21/0.53    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k9_tmap_1(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK0)) | ~spl5_14),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f704])).
% 0.21/0.53  fof(f704,plain,(
% 0.21/0.53    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k9_tmap_1(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | ~spl5_14),
% 0.21/0.53    inference(resolution,[],[f337,f107])).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 = X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f61])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 0.21/0.53    inference(flattening,[],[f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).
% 0.21/0.53  fof(f337,plain,(
% 0.21/0.53    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) | ~spl5_14),
% 0.21/0.53    inference(avatar_component_clause,[],[f335])).
% 0.21/0.53  fof(f808,plain,(
% 0.21/0.53    v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1)) | ~v3_pre_topc(u1_struct_0(sK1),sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f807,f62])).
% 0.21/0.53  fof(f807,plain,(
% 0.21/0.53    v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1)) | ~v3_pre_topc(u1_struct_0(sK1),sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f806,f63])).
% 0.21/0.53  fof(f806,plain,(
% 0.21/0.53    v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1)) | ~v3_pre_topc(u1_struct_0(sK1),sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f805,f64])).
% 0.21/0.53  fof(f805,plain,(
% 0.21/0.53    v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1)) | ~v3_pre_topc(u1_struct_0(sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f253,f160])).
% 0.21/0.53  fof(f253,plain,(
% 0.21/0.53    v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1)) | ~v3_pre_topc(u1_struct_0(sK1),sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(superposition,[],[f94,f212])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1))) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | (~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1)))) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_tmap_1)).
% 0.21/0.53  fof(f804,plain,(
% 0.21/0.53    spl5_10 | ~spl5_5 | ~spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_9 | ~spl5_14 | spl5_16),
% 0.21/0.53    inference(avatar_split_clause,[],[f803,f357,f335,f227,f137,f129,f125,f133,f231])).
% 0.21/0.53  fof(f803,plain,(
% 0.21/0.53    ~v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1)) | v3_pre_topc(u1_struct_0(sK1),sK0) | (~spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_9 | ~spl5_14 | spl5_16)),
% 0.21/0.53    inference(subsumption_resolution,[],[f802,f126])).
% 0.21/0.53  fof(f802,plain,(
% 0.21/0.53    ~v1_funct_1(k9_tmap_1(sK0,sK1)) | ~v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1)) | v3_pre_topc(u1_struct_0(sK1),sK0) | (~spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_9 | ~spl5_14 | spl5_16)),
% 0.21/0.53    inference(forward_demodulation,[],[f801,f712])).
% 0.21/0.53  fof(f801,plain,(
% 0.21/0.53    ~v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1)) | v3_pre_topc(u1_struct_0(sK1),sK0) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | (~spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_9 | ~spl5_14 | spl5_16)),
% 0.21/0.53    inference(subsumption_resolution,[],[f800,f287])).
% 0.21/0.53  fof(f800,plain,(
% 0.21/0.53    ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1)) | v3_pre_topc(u1_struct_0(sK1),sK0) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | (~spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_9 | ~spl5_14 | spl5_16)),
% 0.21/0.53    inference(forward_demodulation,[],[f799,f712])).
% 0.21/0.53  fof(f799,plain,(
% 0.21/0.53    ~v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1)) | v3_pre_topc(u1_struct_0(sK1),sK0) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | (~spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_9 | ~spl5_14 | spl5_16)),
% 0.21/0.53    inference(forward_demodulation,[],[f798,f285])).
% 0.21/0.53  fof(f798,plain,(
% 0.21/0.53    ~v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1)) | v3_pre_topc(u1_struct_0(sK1),sK0) | ~v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | (~spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_9 | ~spl5_14 | spl5_16)),
% 0.21/0.53    inference(forward_demodulation,[],[f797,f712])).
% 0.21/0.53  fof(f797,plain,(
% 0.21/0.53    v3_pre_topc(u1_struct_0(sK1),sK0) | ~v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1)) | ~v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | (~spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_9 | ~spl5_14 | spl5_16)),
% 0.21/0.53    inference(subsumption_resolution,[],[f796,f473])).
% 0.21/0.53  fof(f796,plain,(
% 0.21/0.53    ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | v3_pre_topc(u1_struct_0(sK1),sK0) | ~v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1)) | ~v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | (~spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_9 | ~spl5_14 | spl5_16)),
% 0.21/0.53    inference(forward_demodulation,[],[f795,f712])).
% 0.21/0.53  fof(f795,plain,(
% 0.21/0.53    ~m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | v3_pre_topc(u1_struct_0(sK1),sK0) | ~v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1)) | ~v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))),
% 0.21/0.53    inference(forward_demodulation,[],[f794,f285])).
% 0.21/0.53  fof(f794,plain,(
% 0.21/0.53    ~m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | v3_pre_topc(u1_struct_0(sK1),sK0) | ~v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1)) | ~v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f793,f62])).
% 0.21/0.53  fof(f793,plain,(
% 0.21/0.53    ~m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | v3_pre_topc(u1_struct_0(sK1),sK0) | ~v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1)) | ~v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f792,f63])).
% 0.21/0.53  fof(f792,plain,(
% 0.21/0.53    ~m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | v3_pre_topc(u1_struct_0(sK1),sK0) | ~v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1)) | ~v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f791,f64])).
% 0.21/0.53  fof(f791,plain,(
% 0.21/0.53    ~m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | v3_pre_topc(u1_struct_0(sK1),sK0) | ~v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1)) | ~v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f254,f160])).
% 0.21/0.53  fof(f254,plain,(
% 0.21/0.53    ~m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | v3_pre_topc(u1_struct_0(sK1),sK0) | ~v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1)) | ~v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(superposition,[],[f96,f212])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | v3_pre_topc(X1,X0) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f60])).
% 0.21/0.53  fof(f476,plain,(
% 0.21/0.53    ~spl5_6 | spl5_13),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f475])).
% 0.21/0.53  fof(f475,plain,(
% 0.21/0.53    $false | (~spl5_6 | spl5_13)),
% 0.21/0.53    inference(subsumption_resolution,[],[f333,f473])).
% 0.21/0.53  fof(f333,plain,(
% 0.21/0.53    ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | spl5_13),
% 0.21/0.53    inference(avatar_component_clause,[],[f331])).
% 0.21/0.53  fof(f331,plain,(
% 0.21/0.53    spl5_13 <=> m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.53  fof(f471,plain,(
% 0.21/0.53    spl5_6),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f470])).
% 0.21/0.53  fof(f470,plain,(
% 0.21/0.53    $false | spl5_6),
% 0.21/0.53    inference(subsumption_resolution,[],[f469,f286])).
% 0.21/0.53  fof(f286,plain,(
% 0.21/0.53    ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | spl5_6),
% 0.21/0.53    inference(backward_demodulation,[],[f139,f285])).
% 0.21/0.53  fof(f139,plain,(
% 0.21/0.53    ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | spl5_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f137])).
% 0.21/0.53  fof(f469,plain,(
% 0.21/0.53    m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 0.21/0.53    inference(forward_demodulation,[],[f193,f285])).
% 0.21/0.53  fof(f193,plain,(
% 0.21/0.53    m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))),
% 0.21/0.53    inference(subsumption_resolution,[],[f192,f62])).
% 0.21/0.53  fof(f192,plain,(
% 0.21/0.53    m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f191,f63])).
% 0.21/0.53  fof(f191,plain,(
% 0.21/0.53    m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f159,f64])).
% 0.21/0.53  fof(f159,plain,(
% 0.21/0.53    m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(resolution,[],[f65,f103])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_tmap_1)).
% 0.21/0.53  fof(f467,plain,(
% 0.21/0.53    ~spl5_4 | spl5_12),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f466])).
% 0.21/0.53  fof(f466,plain,(
% 0.21/0.53    $false | (~spl5_4 | spl5_12)),
% 0.21/0.53    inference(subsumption_resolution,[],[f329,f287])).
% 0.21/0.53  fof(f329,plain,(
% 0.21/0.53    ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | spl5_12),
% 0.21/0.53    inference(avatar_component_clause,[],[f327])).
% 0.21/0.53  fof(f327,plain,(
% 0.21/0.53    spl5_12 <=> v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.53  fof(f464,plain,(
% 0.21/0.53    ~spl5_16),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f463])).
% 0.21/0.53  fof(f463,plain,(
% 0.21/0.53    $false | ~spl5_16),
% 0.21/0.53    inference(subsumption_resolution,[],[f462,f62])).
% 0.21/0.53  fof(f462,plain,(
% 0.21/0.53    v2_struct_0(sK0) | ~spl5_16),
% 0.21/0.53    inference(subsumption_resolution,[],[f461,f149])).
% 0.21/0.53  fof(f149,plain,(
% 0.21/0.53    l1_struct_0(sK0)),
% 0.21/0.53    inference(resolution,[],[f64,f75])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.53  fof(f461,plain,(
% 0.21/0.53    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl5_16),
% 0.21/0.53    inference(resolution,[],[f358,f81])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.53  fof(f358,plain,(
% 0.21/0.53    v1_xboole_0(u1_struct_0(sK0)) | ~spl5_16),
% 0.21/0.53    inference(avatar_component_clause,[],[f357])).
% 0.21/0.53  fof(f338,plain,(
% 0.21/0.53    ~spl5_12 | ~spl5_13 | spl5_14 | ~spl5_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f325,f125,f335,f331,f327])).
% 0.21/0.53  fof(f325,plain,(
% 0.21/0.53    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) | ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~spl5_3),
% 0.21/0.53    inference(forward_demodulation,[],[f324,f285])).
% 0.21/0.53  fof(f324,plain,(
% 0.21/0.53    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) | ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~spl5_3),
% 0.21/0.53    inference(forward_demodulation,[],[f323,f212])).
% 0.21/0.53  fof(f323,plain,(
% 0.21/0.53    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) | ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~spl5_3),
% 0.21/0.53    inference(subsumption_resolution,[],[f322,f62])).
% 0.21/0.53  fof(f322,plain,(
% 0.21/0.53    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) | ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~spl5_3),
% 0.21/0.53    inference(subsumption_resolution,[],[f321,f63])).
% 0.21/0.53  fof(f321,plain,(
% 0.21/0.53    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) | ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_3),
% 0.21/0.53    inference(subsumption_resolution,[],[f320,f64])).
% 0.21/0.53  fof(f320,plain,(
% 0.21/0.53    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) | ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_3),
% 0.21/0.53    inference(subsumption_resolution,[],[f319,f65])).
% 0.21/0.53  fof(f319,plain,(
% 0.21/0.53    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) | ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_3),
% 0.21/0.53    inference(subsumption_resolution,[],[f318,f126])).
% 0.21/0.53  fof(f318,plain,(
% 0.21/0.53    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) | ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k9_tmap_1(sK0,sK1)) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f289,f160])).
% 0.21/0.53  fof(f289,plain,(
% 0.21/0.53    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k9_tmap_1(sK0,sK1)) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(superposition,[],[f113,f285])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f112])).
% 0.21/0.53  fof(f112,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),X2,k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k9_tmap_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f86])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k9_tmap_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK4(X0,X1,X2))),X2,k7_tmap_1(X0,sK4(X0,X1,X2))) & u1_struct_0(X1) = sK4(X0,X1,X2) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f56,f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ! [X2,X1,X0] : (? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK4(X0,X1,X2))),X2,k7_tmap_1(X0,sK4(X0,X1,X2))) & u1_struct_0(X1) = sK4(X0,X1,X2) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(rectify,[],[f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : ((r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(X2)) => (k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_tmap_1)).
% 0.21/0.53  fof(f246,plain,(
% 0.21/0.53    spl5_4),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f245])).
% 0.21/0.53  fof(f245,plain,(
% 0.21/0.53    $false | spl5_4),
% 0.21/0.53    inference(subsumption_resolution,[],[f244,f62])).
% 0.21/0.53  fof(f244,plain,(
% 0.21/0.53    v2_struct_0(sK0) | spl5_4),
% 0.21/0.53    inference(subsumption_resolution,[],[f243,f63])).
% 0.21/0.53  fof(f243,plain,(
% 0.21/0.53    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl5_4),
% 0.21/0.53    inference(subsumption_resolution,[],[f242,f64])).
% 0.21/0.53  fof(f242,plain,(
% 0.21/0.53    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl5_4),
% 0.21/0.53    inference(subsumption_resolution,[],[f241,f65])).
% 0.21/0.53  fof(f241,plain,(
% 0.21/0.53    ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl5_4),
% 0.21/0.53    inference(resolution,[],[f131,f102])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f131,plain,(
% 0.21/0.53    ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | spl5_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f129])).
% 0.21/0.53  fof(f198,plain,(
% 0.21/0.53    spl5_3),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f197])).
% 0.21/0.53  fof(f197,plain,(
% 0.21/0.53    $false | spl5_3),
% 0.21/0.53    inference(subsumption_resolution,[],[f190,f127])).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    ~v1_funct_1(k9_tmap_1(sK0,sK1)) | spl5_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f125])).
% 0.21/0.53  fof(f190,plain,(
% 0.21/0.53    v1_funct_1(k9_tmap_1(sK0,sK1))),
% 0.21/0.53    inference(subsumption_resolution,[],[f189,f62])).
% 0.21/0.53  fof(f189,plain,(
% 0.21/0.53    v1_funct_1(k9_tmap_1(sK0,sK1)) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f188,f63])).
% 0.21/0.53  fof(f188,plain,(
% 0.21/0.53    v1_funct_1(k9_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f158,f64])).
% 0.21/0.53  fof(f158,plain,(
% 0.21/0.53    v1_funct_1(k9_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(resolution,[],[f65,f101])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v1_funct_1(k9_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f195,plain,(
% 0.21/0.53    spl5_2),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f194])).
% 0.21/0.53  fof(f194,plain,(
% 0.21/0.53    $false | spl5_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f123,f65])).
% 0.21/0.53  fof(f123,plain,(
% 0.21/0.53    ~m1_pre_topc(sK1,sK0) | spl5_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f121])).
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    spl5_2 <=> m1_pre_topc(sK1,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.53  fof(f172,plain,(
% 0.21/0.53    spl5_1 | spl5_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f167,f169,f117])).
% 0.21/0.53  fof(f167,plain,(
% 0.21/0.53    u1_struct_0(sK1) = sK2(sK0,sK1) | v1_tsep_1(sK1,sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f152,f64])).
% 0.21/0.53  fof(f152,plain,(
% 0.21/0.53    u1_struct_0(sK1) = sK2(sK0,sK1) | v1_tsep_1(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f65,f79])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | u1_struct_0(X1) = sK2(X0,X1) | v1_tsep_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f50])).
% 0.21/0.53  fof(f144,plain,(
% 0.21/0.53    spl5_1 | spl5_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f70,f133,f117])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1)) | v1_tsep_1(sK1,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f46])).
% 0.21/0.53  fof(f140,plain,(
% 0.21/0.53    ~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f74,f137,f133,f129,f125,f121,f117])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1)) | ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(k9_tmap_1(sK0,sK1)) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f46])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (14469)------------------------------
% 0.21/0.53  % (14469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (14469)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (14469)Memory used [KB]: 11129
% 0.21/0.53  % (14469)Time elapsed: 0.113 s
% 0.21/0.53  % (14469)------------------------------
% 0.21/0.53  % (14469)------------------------------
% 0.21/0.53  % (14473)Refutation not found, incomplete strategy% (14473)------------------------------
% 0.21/0.53  % (14473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (14473)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (14473)Memory used [KB]: 6140
% 0.21/0.53  % (14473)Time elapsed: 0.125 s
% 0.21/0.53  % (14473)------------------------------
% 0.21/0.53  % (14473)------------------------------
% 0.21/0.53  % (14467)Success in time 0.171 s
%------------------------------------------------------------------------------
