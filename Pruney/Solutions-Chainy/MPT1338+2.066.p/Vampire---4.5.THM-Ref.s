%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:10 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :  174 (8619 expanded)
%              Number of leaves         :   24 (3088 expanded)
%              Depth                    :   31
%              Number of atoms          :  492 (72045 expanded)
%              Number of equality atoms :  165 (22962 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f724,plain,(
    $false ),
    inference(subsumption_resolution,[],[f723,f599])).

fof(f599,plain,(
    k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f598,f470])).

fof(f470,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    inference(forward_demodulation,[],[f469,f343])).

fof(f343,plain,(
    k2_funct_1(sK2) = k3_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    inference(forward_demodulation,[],[f331,f175])).

fof(f175,plain,(
    k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f174,f66])).

fof(f66,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,
    ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
      | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) )
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f57,f56,f55])).

fof(f55,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                  | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
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
              ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))
              | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) )
            & v2_funct_1(X2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))
            | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) )
          & v2_funct_1(X2)
          & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ? [X2] :
        ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))
          | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) )
        & v2_funct_1(X2)
        & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
        | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) )
      & v2_funct_1(sK2)
      & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
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
                 => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                    & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

fof(f174,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f167,f70])).

fof(f70,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f167,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f147,f78])).

fof(f78,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(X0) = k4_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f147,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f139,f80])).

fof(f80,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f139,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(resolution,[],[f68,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f68,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f58])).

fof(f331,plain,(
    k4_relat_1(sK2) = k3_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    inference(resolution,[],[f314,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

fof(f314,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f268,f303])).

fof(f303,plain,(
    k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f302,f147])).

fof(f302,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f301,f196])).

fof(f196,plain,(
    v4_relat_1(sK2,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f193,f63])).

fof(f63,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f193,plain,
    ( v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f136,f72])).

fof(f72,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f136,plain,(
    v4_relat_1(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f68,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f301,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f281,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f281,plain,(
    v1_partfun1(sK2,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f280,f257])).

fof(f257,plain,(
    ~ v1_xboole_0(k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f107,f157])).

fof(f157,plain,(
    k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f152,f68])).

fof(f152,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(superposition,[],[f69,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f69,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f107,plain,(
    ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f105,f64])).

fof(f64,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f105,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f65,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f65,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f280,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | v1_xboole_0(k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f279,f66])).

fof(f279,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f270,f261])).

fof(f261,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f254,f157])).

% (22588)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
fof(f254,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f206,f106])).

fof(f106,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f65,f72])).

fof(f206,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f67,f103])).

fof(f103,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(resolution,[],[f63,f72])).

fof(f67,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f58])).

fof(f270,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(k2_relat_1(sK2)) ),
    inference(resolution,[],[f268,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f268,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    inference(forward_demodulation,[],[f253,f157])).

fof(f253,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f205,f106])).

fof(f205,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f68,f103])).

fof(f469,plain,(
    m1_subset_1(k3_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    inference(forward_demodulation,[],[f468,f256])).

fof(f256,plain,(
    u1_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f106,f157])).

fof(f468,plain,(
    m1_subset_1(k3_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2)))) ),
    inference(forward_demodulation,[],[f135,f311])).

fof(f311,plain,(
    u1_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f103,f303])).

fof(f135,plain,(
    m1_subset_1(k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f68,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_relset_1)).

fof(f598,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    inference(subsumption_resolution,[],[f596,f566])).

fof(f566,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f565,f523])).

fof(f523,plain,(
    k1_relat_1(sK2) = k9_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f522,f147])).

fof(f522,plain,
    ( k1_relat_1(sK2) = k9_relat_1(k2_funct_1(sK2),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f519,f101])).

fof(f101,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
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

fof(f519,plain,
    ( k1_relat_1(sK2) = k9_relat_1(k2_funct_1(sK2),k2_relat_1(sK2))
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f517,f74])).

fof(f74,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f517,plain,(
    ! [X3] :
      ( k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X3)) = X3
      | ~ r1_tarski(X3,k1_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f119,f147])).

fof(f119,plain,(
    ! [X3] :
      ( k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X3)) = X3
      | ~ r1_tarski(X3,k1_relat_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f115,f66])).

fof(f115,plain,(
    ! [X3] :
      ( k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X3)) = X3
      | ~ r1_tarski(X3,k1_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f70,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
      | ~ r1_tarski(X1,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
          | ~ r1_tarski(X1,k1_relat_1(X0))
          | ~ v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
          | ~ r1_tarski(X1,k1_relat_1(X0))
          | ~ v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( r1_tarski(X1,k1_relat_1(X0))
            & v2_funct_1(X0) )
         => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).

fof(f565,plain,(
    k9_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f564,f481])).

fof(f481,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f479,f80])).

fof(f479,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))) ),
    inference(resolution,[],[f470,f76])).

fof(f564,plain,
    ( k9_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[],[f83,f516])).

fof(f516,plain,(
    k2_funct_1(sK2) = k7_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f514,f481])).

fof(f514,plain,
    ( k2_funct_1(sK2) = k7_relat_1(k2_funct_1(sK2),k2_relat_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f476,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f476,plain,(
    v4_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) ),
    inference(resolution,[],[f470,f97])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f596,plain,
    ( k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    inference(superposition,[],[f594,f95])).

fof(f594,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f454,f470])).

fof(f454,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    inference(superposition,[],[f446,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f446,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f444,f355])).

fof(f355,plain,(
    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f354,f66])).

fof(f354,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f353,f313])).

fof(f313,plain,(
    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f261,f303])).

fof(f353,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f352,f314])).

fof(f352,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f350,f70])).

fof(f350,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f349])).

fof(f349,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f98,f316])).

fof(f316,plain,(
    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    inference(backward_demodulation,[],[f285,f303])).

fof(f285,plain,(
    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(forward_demodulation,[],[f252,f157])).

fof(f252,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f204,f106])).

fof(f204,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f69,f103])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f444,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) ),
    inference(backward_demodulation,[],[f319,f355])).

fof(f319,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) ),
    inference(forward_demodulation,[],[f317,f303])).

fof(f317,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    inference(backward_demodulation,[],[f293,f303])).

% (22597)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
fof(f293,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    inference(forward_demodulation,[],[f292,f157])).

fof(f292,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(forward_demodulation,[],[f255,f157])).

fof(f255,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(forward_demodulation,[],[f251,f106])).

fof(f251,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(backward_demodulation,[],[f207,f106])).

fof(f207,plain,
    ( k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(forward_demodulation,[],[f203,f103])).

fof(f203,plain,
    ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(backward_demodulation,[],[f71,f103])).

fof(f71,plain,
    ( k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f58])).

fof(f723,plain,(
    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f722,f164])).

fof(f164,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(resolution,[],[f147,f74])).

fof(f722,plain,(
    k9_relat_1(sK2,k1_relat_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f721,f566])).

fof(f721,plain,(
    k1_relat_1(k2_funct_1(sK2)) = k9_relat_1(sK2,k2_relat_1(k2_funct_1(sK2))) ),
    inference(subsumption_resolution,[],[f460,f481])).

fof(f460,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k9_relat_1(sK2,k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[],[f459,f73])).

fof(f73,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f459,plain,(
    ! [X2] : k9_relat_1(sK2,X2) = k10_relat_1(k2_funct_1(sK2),X2) ),
    inference(subsumption_resolution,[],[f118,f147])).

fof(f118,plain,(
    ! [X2] :
      ( k9_relat_1(sK2,X2) = k10_relat_1(k2_funct_1(sK2),X2)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f114,f66])).

fof(f114,plain,(
    ! [X2] :
      ( k9_relat_1(sK2,X2) = k10_relat_1(k2_funct_1(sK2),X2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f70,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:06:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.54  % (22574)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.55  % (22578)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.55  % (22578)Refutation not found, incomplete strategy% (22578)------------------------------
% 0.21/0.55  % (22578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (22578)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (22578)Memory used [KB]: 10618
% 0.21/0.55  % (22578)Time elapsed: 0.117 s
% 0.21/0.55  % (22578)------------------------------
% 0.21/0.55  % (22578)------------------------------
% 0.21/0.55  % (22594)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.56  % (22590)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.56  % (22586)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.56  % (22576)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.56  % (22581)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.56  % (22595)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.57  % (22577)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.60/0.57  % (22584)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.60/0.57  % (22573)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.60/0.57  % (22587)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.60/0.57  % (22575)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.60/0.57  % (22572)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.60/0.58  % (22590)Refutation found. Thanks to Tanya!
% 1.60/0.58  % SZS status Theorem for theBenchmark
% 1.60/0.58  % SZS output start Proof for theBenchmark
% 1.60/0.58  fof(f724,plain,(
% 1.60/0.58    $false),
% 1.60/0.58    inference(subsumption_resolution,[],[f723,f599])).
% 1.60/0.58  fof(f599,plain,(
% 1.60/0.58    k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))),
% 1.60/0.58    inference(subsumption_resolution,[],[f598,f470])).
% 1.60/0.58  fof(f470,plain,(
% 1.60/0.58    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 1.60/0.58    inference(forward_demodulation,[],[f469,f343])).
% 1.60/0.58  fof(f343,plain,(
% 1.60/0.58    k2_funct_1(sK2) = k3_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 1.60/0.58    inference(forward_demodulation,[],[f331,f175])).
% 1.60/0.58  fof(f175,plain,(
% 1.60/0.58    k2_funct_1(sK2) = k4_relat_1(sK2)),
% 1.60/0.58    inference(subsumption_resolution,[],[f174,f66])).
% 1.60/0.58  fof(f66,plain,(
% 1.60/0.58    v1_funct_1(sK2)),
% 1.60/0.58    inference(cnf_transformation,[],[f58])).
% 1.60/0.58  fof(f58,plain,(
% 1.60/0.58    (((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 1.60/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f57,f56,f55])).
% 1.60/0.58  fof(f55,plain,(
% 1.60/0.58    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 1.60/0.58    introduced(choice_axiom,[])).
% 1.60/0.58  fof(f56,plain,(
% 1.60/0.58    ? [X1] : (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))) & v2_funct_1(X2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))),
% 1.60/0.58    introduced(choice_axiom,[])).
% 1.60/0.58  fof(f57,plain,(
% 1.60/0.58    ? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))) & v2_funct_1(X2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 1.60/0.58    introduced(choice_axiom,[])).
% 1.60/0.58  fof(f27,plain,(
% 1.60/0.58    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 1.60/0.58    inference(flattening,[],[f26])).
% 1.60/0.58  fof(f26,plain,(
% 1.60/0.58    ? [X0] : (? [X1] : (? [X2] : (((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 1.60/0.58    inference(ennf_transformation,[],[f24])).
% 1.60/0.58  fof(f24,negated_conjecture,(
% 1.60/0.58    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 1.60/0.58    inference(negated_conjecture,[],[f23])).
% 1.60/0.58  fof(f23,conjecture,(
% 1.60/0.58    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).
% 1.60/0.58  fof(f174,plain,(
% 1.60/0.58    k2_funct_1(sK2) = k4_relat_1(sK2) | ~v1_funct_1(sK2)),
% 1.60/0.58    inference(subsumption_resolution,[],[f167,f70])).
% 1.60/0.58  fof(f70,plain,(
% 1.60/0.58    v2_funct_1(sK2)),
% 1.60/0.58    inference(cnf_transformation,[],[f58])).
% 1.60/0.58  fof(f167,plain,(
% 1.60/0.58    k2_funct_1(sK2) = k4_relat_1(sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2)),
% 1.60/0.58    inference(resolution,[],[f147,f78])).
% 1.60/0.58  fof(f78,plain,(
% 1.60/0.58    ( ! [X0] : (k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f36])).
% 1.60/0.58  fof(f36,plain,(
% 1.60/0.58    ! [X0] : (k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.60/0.58    inference(flattening,[],[f35])).
% 1.60/0.58  fof(f35,plain,(
% 1.60/0.58    ! [X0] : ((k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.60/0.58    inference(ennf_transformation,[],[f10])).
% 1.60/0.58  fof(f10,axiom,(
% 1.60/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(X0) = k4_relat_1(X0)))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 1.60/0.58  fof(f147,plain,(
% 1.60/0.58    v1_relat_1(sK2)),
% 1.60/0.58    inference(subsumption_resolution,[],[f139,f80])).
% 1.60/0.58  fof(f80,plain,(
% 1.60/0.58    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.60/0.58    inference(cnf_transformation,[],[f4])).
% 1.60/0.58  fof(f4,axiom,(
% 1.60/0.58    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.60/0.58  fof(f139,plain,(
% 1.60/0.58    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))),
% 1.60/0.58    inference(resolution,[],[f68,f76])).
% 1.60/0.58  fof(f76,plain,(
% 1.60/0.58    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f32])).
% 1.60/0.58  fof(f32,plain,(
% 1.60/0.58    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.60/0.58    inference(ennf_transformation,[],[f3])).
% 1.60/0.58  fof(f3,axiom,(
% 1.60/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.60/0.58  fof(f68,plain,(
% 1.60/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.60/0.58    inference(cnf_transformation,[],[f58])).
% 1.60/0.58  fof(f331,plain,(
% 1.60/0.58    k4_relat_1(sK2) = k3_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 1.60/0.58    inference(resolution,[],[f314,f93])).
% 1.60/0.58  fof(f93,plain,(
% 1.60/0.58    ( ! [X2,X0,X1] : (k3_relset_1(X0,X1,X2) = k4_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.60/0.58    inference(cnf_transformation,[],[f48])).
% 1.60/0.58  fof(f48,plain,(
% 1.60/0.58    ! [X0,X1,X2] : (k3_relset_1(X0,X1,X2) = k4_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.60/0.58    inference(ennf_transformation,[],[f17])).
% 1.60/0.58  fof(f17,axiom,(
% 1.60/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k3_relset_1(X0,X1,X2) = k4_relat_1(X2))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_relset_1)).
% 1.60/0.58  fof(f314,plain,(
% 1.60/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 1.60/0.58    inference(backward_demodulation,[],[f268,f303])).
% 1.60/0.58  fof(f303,plain,(
% 1.60/0.58    k2_struct_0(sK0) = k1_relat_1(sK2)),
% 1.60/0.58    inference(subsumption_resolution,[],[f302,f147])).
% 1.60/0.58  fof(f302,plain,(
% 1.60/0.58    k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2)),
% 1.60/0.58    inference(subsumption_resolution,[],[f301,f196])).
% 1.60/0.58  fof(f196,plain,(
% 1.60/0.58    v4_relat_1(sK2,k2_struct_0(sK0))),
% 1.60/0.58    inference(subsumption_resolution,[],[f193,f63])).
% 1.60/0.58  fof(f63,plain,(
% 1.60/0.58    l1_struct_0(sK0)),
% 1.60/0.58    inference(cnf_transformation,[],[f58])).
% 1.60/0.58  fof(f193,plain,(
% 1.60/0.58    v4_relat_1(sK2,k2_struct_0(sK0)) | ~l1_struct_0(sK0)),
% 1.60/0.58    inference(superposition,[],[f136,f72])).
% 1.60/0.58  fof(f72,plain,(
% 1.60/0.58    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f28])).
% 1.60/0.58  fof(f28,plain,(
% 1.60/0.58    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.60/0.58    inference(ennf_transformation,[],[f20])).
% 1.60/0.58  fof(f20,axiom,(
% 1.60/0.58    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 1.60/0.58  fof(f136,plain,(
% 1.60/0.58    v4_relat_1(sK2,u1_struct_0(sK0))),
% 1.60/0.58    inference(resolution,[],[f68,f97])).
% 1.60/0.58  fof(f97,plain,(
% 1.60/0.58    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.60/0.58    inference(cnf_transformation,[],[f52])).
% 1.60/0.58  fof(f52,plain,(
% 1.60/0.58    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.60/0.58    inference(ennf_transformation,[],[f25])).
% 1.60/0.58  fof(f25,plain,(
% 1.60/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.60/0.58    inference(pure_predicate_removal,[],[f13])).
% 1.60/0.58  fof(f13,axiom,(
% 1.60/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.60/0.58  fof(f301,plain,(
% 1.60/0.58    k2_struct_0(sK0) = k1_relat_1(sK2) | ~v4_relat_1(sK2,k2_struct_0(sK0)) | ~v1_relat_1(sK2)),
% 1.60/0.58    inference(resolution,[],[f281,f86])).
% 1.60/0.58  fof(f86,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f59])).
% 1.60/0.58  fof(f59,plain,(
% 1.60/0.58    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.60/0.58    inference(nnf_transformation,[],[f47])).
% 1.60/0.58  fof(f47,plain,(
% 1.60/0.58    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.60/0.58    inference(flattening,[],[f46])).
% 1.60/0.58  fof(f46,plain,(
% 1.60/0.58    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.60/0.58    inference(ennf_transformation,[],[f19])).
% 1.60/0.58  fof(f19,axiom,(
% 1.60/0.58    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 1.60/0.58  fof(f281,plain,(
% 1.60/0.58    v1_partfun1(sK2,k2_struct_0(sK0))),
% 1.60/0.58    inference(subsumption_resolution,[],[f280,f257])).
% 1.60/0.58  fof(f257,plain,(
% 1.60/0.58    ~v1_xboole_0(k2_relat_1(sK2))),
% 1.60/0.58    inference(backward_demodulation,[],[f107,f157])).
% 1.60/0.58  fof(f157,plain,(
% 1.60/0.58    k2_struct_0(sK1) = k2_relat_1(sK2)),
% 1.60/0.58    inference(subsumption_resolution,[],[f152,f68])).
% 1.60/0.58  fof(f152,plain,(
% 1.60/0.58    k2_struct_0(sK1) = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.60/0.58    inference(superposition,[],[f69,f95])).
% 1.60/0.58  fof(f95,plain,(
% 1.60/0.58    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.60/0.58    inference(cnf_transformation,[],[f50])).
% 1.60/0.58  fof(f50,plain,(
% 1.60/0.58    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.60/0.58    inference(ennf_transformation,[],[f16])).
% 1.60/0.58  fof(f16,axiom,(
% 1.60/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.60/0.58  fof(f69,plain,(
% 1.60/0.58    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 1.60/0.58    inference(cnf_transformation,[],[f58])).
% 1.60/0.58  fof(f107,plain,(
% 1.60/0.58    ~v1_xboole_0(k2_struct_0(sK1))),
% 1.60/0.58    inference(subsumption_resolution,[],[f105,f64])).
% 1.60/0.58  fof(f64,plain,(
% 1.60/0.58    ~v2_struct_0(sK1)),
% 1.60/0.58    inference(cnf_transformation,[],[f58])).
% 1.60/0.58  fof(f105,plain,(
% 1.60/0.58    ~v1_xboole_0(k2_struct_0(sK1)) | v2_struct_0(sK1)),
% 1.60/0.58    inference(resolution,[],[f65,f77])).
% 1.60/0.58  fof(f77,plain,(
% 1.60/0.58    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f34])).
% 1.60/0.58  fof(f34,plain,(
% 1.60/0.58    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.60/0.58    inference(flattening,[],[f33])).
% 1.60/0.58  fof(f33,plain,(
% 1.60/0.58    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.60/0.58    inference(ennf_transformation,[],[f21])).
% 1.60/0.58  fof(f21,axiom,(
% 1.60/0.58    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).
% 1.60/0.58  fof(f65,plain,(
% 1.60/0.58    l1_struct_0(sK1)),
% 1.60/0.58    inference(cnf_transformation,[],[f58])).
% 1.60/0.58  fof(f280,plain,(
% 1.60/0.58    v1_partfun1(sK2,k2_struct_0(sK0)) | v1_xboole_0(k2_relat_1(sK2))),
% 1.60/0.58    inference(subsumption_resolution,[],[f279,f66])).
% 1.60/0.58  fof(f279,plain,(
% 1.60/0.58    v1_partfun1(sK2,k2_struct_0(sK0)) | ~v1_funct_1(sK2) | v1_xboole_0(k2_relat_1(sK2))),
% 1.60/0.58    inference(subsumption_resolution,[],[f270,f261])).
% 1.60/0.58  fof(f261,plain,(
% 1.60/0.58    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 1.60/0.58    inference(forward_demodulation,[],[f254,f157])).
% 1.60/0.58  % (22588)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.60/0.58  fof(f254,plain,(
% 1.60/0.58    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 1.60/0.58    inference(backward_demodulation,[],[f206,f106])).
% 1.60/0.58  fof(f106,plain,(
% 1.60/0.58    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 1.60/0.58    inference(resolution,[],[f65,f72])).
% 1.60/0.58  fof(f206,plain,(
% 1.60/0.58    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))),
% 1.60/0.58    inference(backward_demodulation,[],[f67,f103])).
% 1.60/0.58  fof(f103,plain,(
% 1.60/0.58    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 1.60/0.58    inference(resolution,[],[f63,f72])).
% 1.60/0.58  fof(f67,plain,(
% 1.60/0.58    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.60/0.58    inference(cnf_transformation,[],[f58])).
% 1.60/0.58  fof(f270,plain,(
% 1.60/0.58    v1_partfun1(sK2,k2_struct_0(sK0)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | v1_xboole_0(k2_relat_1(sK2))),
% 1.60/0.58    inference(resolution,[],[f268,f82])).
% 1.60/0.58  fof(f82,plain,(
% 1.60/0.58    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f40])).
% 1.60/0.58  fof(f40,plain,(
% 1.60/0.58    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.60/0.58    inference(flattening,[],[f39])).
% 1.60/0.58  fof(f39,plain,(
% 1.60/0.58    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.60/0.58    inference(ennf_transformation,[],[f18])).
% 1.60/0.58  fof(f18,axiom,(
% 1.60/0.58    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 1.60/0.58  fof(f268,plain,(
% 1.60/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 1.60/0.58    inference(forward_demodulation,[],[f253,f157])).
% 1.60/0.58  fof(f253,plain,(
% 1.60/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 1.60/0.58    inference(backward_demodulation,[],[f205,f106])).
% 1.60/0.58  fof(f205,plain,(
% 1.60/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1))))),
% 1.60/0.58    inference(backward_demodulation,[],[f68,f103])).
% 1.60/0.58  fof(f469,plain,(
% 1.60/0.58    m1_subset_1(k3_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 1.60/0.58    inference(forward_demodulation,[],[f468,f256])).
% 1.60/0.58  fof(f256,plain,(
% 1.60/0.58    u1_struct_0(sK1) = k2_relat_1(sK2)),
% 1.60/0.58    inference(backward_demodulation,[],[f106,f157])).
% 1.60/0.58  fof(f468,plain,(
% 1.60/0.58    m1_subset_1(k3_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))))),
% 1.60/0.58    inference(forward_demodulation,[],[f135,f311])).
% 1.60/0.58  fof(f311,plain,(
% 1.60/0.58    u1_struct_0(sK0) = k1_relat_1(sK2)),
% 1.60/0.58    inference(backward_demodulation,[],[f103,f303])).
% 1.60/0.58  fof(f135,plain,(
% 1.60/0.58    m1_subset_1(k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 1.60/0.58    inference(resolution,[],[f68,f96])).
% 1.60/0.58  fof(f96,plain,(
% 1.60/0.58    ( ! [X2,X0,X1] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.60/0.58    inference(cnf_transformation,[],[f51])).
% 1.60/0.58  fof(f51,plain,(
% 1.60/0.58    ! [X0,X1,X2] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.60/0.58    inference(ennf_transformation,[],[f14])).
% 1.60/0.58  fof(f14,axiom,(
% 1.60/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_relset_1)).
% 1.60/0.58  fof(f598,plain,(
% 1.60/0.58    k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 1.60/0.58    inference(subsumption_resolution,[],[f596,f566])).
% 1.60/0.58  fof(f566,plain,(
% 1.60/0.58    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.60/0.58    inference(forward_demodulation,[],[f565,f523])).
% 1.60/0.58  fof(f523,plain,(
% 1.60/0.58    k1_relat_1(sK2) = k9_relat_1(k2_funct_1(sK2),k2_relat_1(sK2))),
% 1.60/0.58    inference(subsumption_resolution,[],[f522,f147])).
% 1.60/0.58  fof(f522,plain,(
% 1.60/0.58    k1_relat_1(sK2) = k9_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 1.60/0.58    inference(subsumption_resolution,[],[f519,f101])).
% 1.60/0.58  fof(f101,plain,(
% 1.60/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.60/0.58    inference(equality_resolution,[],[f88])).
% 1.60/0.58  fof(f88,plain,(
% 1.60/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.60/0.58    inference(cnf_transformation,[],[f61])).
% 1.60/0.58  fof(f61,plain,(
% 1.60/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.60/0.58    inference(flattening,[],[f60])).
% 1.60/0.58  fof(f60,plain,(
% 1.60/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.60/0.58    inference(nnf_transformation,[],[f1])).
% 1.60/0.58  fof(f1,axiom,(
% 1.60/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.60/0.58  fof(f519,plain,(
% 1.60/0.58    k1_relat_1(sK2) = k9_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 1.60/0.58    inference(superposition,[],[f517,f74])).
% 1.60/0.58  fof(f74,plain,(
% 1.60/0.58    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f30])).
% 1.60/0.58  fof(f30,plain,(
% 1.60/0.58    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.60/0.58    inference(ennf_transformation,[],[f5])).
% 1.60/0.58  fof(f5,axiom,(
% 1.60/0.58    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 1.60/0.58  fof(f517,plain,(
% 1.60/0.58    ( ! [X3] : (k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X3)) = X3 | ~r1_tarski(X3,k1_relat_1(sK2))) )),
% 1.60/0.58    inference(subsumption_resolution,[],[f119,f147])).
% 1.60/0.58  fof(f119,plain,(
% 1.60/0.58    ( ! [X3] : (k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X3)) = X3 | ~r1_tarski(X3,k1_relat_1(sK2)) | ~v1_relat_1(sK2)) )),
% 1.60/0.58    inference(subsumption_resolution,[],[f115,f66])).
% 1.60/0.58  fof(f115,plain,(
% 1.60/0.58    ( ! [X3] : (k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X3)) = X3 | ~r1_tarski(X3,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 1.60/0.58    inference(resolution,[],[f70,f79])).
% 1.60/0.58  fof(f79,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f38])).
% 1.60/0.58  fof(f38,plain,(
% 1.60/0.58    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.60/0.58    inference(flattening,[],[f37])).
% 1.60/0.58  fof(f37,plain,(
% 1.60/0.58    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | (~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.60/0.58    inference(ennf_transformation,[],[f12])).
% 1.60/0.58  fof(f12,axiom,(
% 1.60/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0)) => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).
% 1.60/0.58  fof(f565,plain,(
% 1.60/0.58    k9_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) = k2_relat_1(k2_funct_1(sK2))),
% 1.60/0.58    inference(subsumption_resolution,[],[f564,f481])).
% 1.60/0.58  fof(f481,plain,(
% 1.60/0.58    v1_relat_1(k2_funct_1(sK2))),
% 1.60/0.58    inference(subsumption_resolution,[],[f479,f80])).
% 1.60/0.58  fof(f479,plain,(
% 1.60/0.58    v1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))),
% 1.60/0.58    inference(resolution,[],[f470,f76])).
% 1.60/0.58  fof(f564,plain,(
% 1.60/0.58    k9_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))),
% 1.60/0.58    inference(superposition,[],[f83,f516])).
% 1.60/0.58  fof(f516,plain,(
% 1.60/0.58    k2_funct_1(sK2) = k7_relat_1(k2_funct_1(sK2),k2_relat_1(sK2))),
% 1.60/0.58    inference(subsumption_resolution,[],[f514,f481])).
% 1.60/0.58  fof(f514,plain,(
% 1.60/0.58    k2_funct_1(sK2) = k7_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))),
% 1.60/0.58    inference(resolution,[],[f476,f85])).
% 1.60/0.58  fof(f85,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f45])).
% 1.60/0.58  fof(f45,plain,(
% 1.60/0.58    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.60/0.58    inference(flattening,[],[f44])).
% 1.60/0.58  fof(f44,plain,(
% 1.60/0.58    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.60/0.58    inference(ennf_transformation,[],[f8])).
% 1.60/0.58  fof(f8,axiom,(
% 1.60/0.58    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 1.60/0.58  fof(f476,plain,(
% 1.60/0.58    v4_relat_1(k2_funct_1(sK2),k2_relat_1(sK2))),
% 1.60/0.58    inference(resolution,[],[f470,f97])).
% 1.60/0.58  fof(f83,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f41])).
% 1.60/0.58  fof(f41,plain,(
% 1.60/0.58    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.60/0.58    inference(ennf_transformation,[],[f6])).
% 1.60/0.58  fof(f6,axiom,(
% 1.60/0.58    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.60/0.58  fof(f596,plain,(
% 1.60/0.58    k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 1.60/0.58    inference(superposition,[],[f594,f95])).
% 1.60/0.58  fof(f594,plain,(
% 1.60/0.58    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))),
% 1.60/0.58    inference(subsumption_resolution,[],[f454,f470])).
% 1.60/0.58  fof(f454,plain,(
% 1.60/0.58    k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 1.60/0.58    inference(superposition,[],[f446,f94])).
% 1.60/0.58  fof(f94,plain,(
% 1.60/0.58    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.60/0.58    inference(cnf_transformation,[],[f49])).
% 1.60/0.58  fof(f49,plain,(
% 1.60/0.58    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.60/0.58    inference(ennf_transformation,[],[f15])).
% 1.60/0.58  fof(f15,axiom,(
% 1.60/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.60/0.58  fof(f446,plain,(
% 1.60/0.58    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 1.60/0.58    inference(forward_demodulation,[],[f444,f355])).
% 1.60/0.58  fof(f355,plain,(
% 1.60/0.58    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 1.60/0.58    inference(subsumption_resolution,[],[f354,f66])).
% 1.60/0.58  fof(f354,plain,(
% 1.60/0.58    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_1(sK2)),
% 1.60/0.58    inference(subsumption_resolution,[],[f353,f313])).
% 1.60/0.58  fof(f313,plain,(
% 1.60/0.58    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 1.60/0.58    inference(backward_demodulation,[],[f261,f303])).
% 1.60/0.58  fof(f353,plain,(
% 1.60/0.58    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2)),
% 1.60/0.58    inference(subsumption_resolution,[],[f352,f314])).
% 1.60/0.58  fof(f352,plain,(
% 1.60/0.58    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2)),
% 1.60/0.58    inference(subsumption_resolution,[],[f350,f70])).
% 1.60/0.58  fof(f350,plain,(
% 1.60/0.58    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2)),
% 1.60/0.58    inference(trivial_inequality_removal,[],[f349])).
% 1.60/0.58  fof(f349,plain,(
% 1.60/0.58    k2_relat_1(sK2) != k2_relat_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2)),
% 1.60/0.58    inference(superposition,[],[f98,f316])).
% 1.60/0.58  fof(f316,plain,(
% 1.60/0.58    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 1.60/0.58    inference(backward_demodulation,[],[f285,f303])).
% 1.60/0.58  fof(f285,plain,(
% 1.60/0.58    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 1.60/0.58    inference(forward_demodulation,[],[f252,f157])).
% 1.60/0.58  fof(f252,plain,(
% 1.60/0.58    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.60/0.58    inference(backward_demodulation,[],[f204,f106])).
% 1.60/0.58  fof(f204,plain,(
% 1.60/0.58    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 1.60/0.58    inference(backward_demodulation,[],[f69,f103])).
% 1.60/0.58  fof(f98,plain,(
% 1.60/0.58    ( ! [X2,X0,X1] : (k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f54])).
% 1.60/0.58  fof(f54,plain,(
% 1.60/0.58    ! [X0,X1,X2] : (k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.60/0.58    inference(flattening,[],[f53])).
% 1.60/0.58  fof(f53,plain,(
% 1.60/0.58    ! [X0,X1,X2] : ((k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.60/0.58    inference(ennf_transformation,[],[f22])).
% 1.60/0.58  fof(f22,axiom,(
% 1.60/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_tops_2(X0,X1,X2) = k2_funct_1(X2)))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 1.60/0.58  fof(f444,plain,(
% 1.60/0.58    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))),
% 1.60/0.58    inference(backward_demodulation,[],[f319,f355])).
% 1.60/0.58  fof(f319,plain,(
% 1.60/0.58    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))),
% 1.60/0.58    inference(forward_demodulation,[],[f317,f303])).
% 1.60/0.58  fof(f317,plain,(
% 1.60/0.58    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))),
% 1.60/0.58    inference(backward_demodulation,[],[f293,f303])).
% 1.60/0.58  % (22597)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.60/0.58  fof(f293,plain,(
% 1.60/0.58    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))),
% 1.60/0.58    inference(forward_demodulation,[],[f292,f157])).
% 1.60/0.58  fof(f292,plain,(
% 1.60/0.58    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 1.60/0.58    inference(forward_demodulation,[],[f255,f157])).
% 1.60/0.58  fof(f255,plain,(
% 1.60/0.58    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 1.60/0.58    inference(forward_demodulation,[],[f251,f106])).
% 1.60/0.58  fof(f251,plain,(
% 1.60/0.58    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 1.60/0.58    inference(backward_demodulation,[],[f207,f106])).
% 1.60/0.58  fof(f207,plain,(
% 1.60/0.58    k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 1.60/0.58    inference(forward_demodulation,[],[f203,f103])).
% 1.60/0.58  fof(f203,plain,(
% 1.60/0.58    k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 1.60/0.58    inference(backward_demodulation,[],[f71,f103])).
% 1.60/0.58  fof(f71,plain,(
% 1.60/0.58    k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 1.60/0.58    inference(cnf_transformation,[],[f58])).
% 1.60/0.58  fof(f723,plain,(
% 1.60/0.58    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 1.60/0.58    inference(forward_demodulation,[],[f722,f164])).
% 1.60/0.58  fof(f164,plain,(
% 1.60/0.58    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))),
% 1.60/0.58    inference(resolution,[],[f147,f74])).
% 1.60/0.58  fof(f722,plain,(
% 1.60/0.58    k9_relat_1(sK2,k1_relat_1(sK2)) = k1_relat_1(k2_funct_1(sK2))),
% 1.60/0.58    inference(forward_demodulation,[],[f721,f566])).
% 1.60/0.58  fof(f721,plain,(
% 1.60/0.58    k1_relat_1(k2_funct_1(sK2)) = k9_relat_1(sK2,k2_relat_1(k2_funct_1(sK2)))),
% 1.60/0.58    inference(subsumption_resolution,[],[f460,f481])).
% 1.60/0.58  fof(f460,plain,(
% 1.60/0.58    k1_relat_1(k2_funct_1(sK2)) = k9_relat_1(sK2,k2_relat_1(k2_funct_1(sK2))) | ~v1_relat_1(k2_funct_1(sK2))),
% 1.60/0.58    inference(superposition,[],[f459,f73])).
% 1.60/0.58  fof(f73,plain,(
% 1.60/0.58    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f29])).
% 1.60/0.58  fof(f29,plain,(
% 1.60/0.58    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.60/0.58    inference(ennf_transformation,[],[f7])).
% 1.60/0.58  fof(f7,axiom,(
% 1.60/0.58    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 1.60/0.58  fof(f459,plain,(
% 1.60/0.58    ( ! [X2] : (k9_relat_1(sK2,X2) = k10_relat_1(k2_funct_1(sK2),X2)) )),
% 1.60/0.58    inference(subsumption_resolution,[],[f118,f147])).
% 1.60/0.58  fof(f118,plain,(
% 1.60/0.58    ( ! [X2] : (k9_relat_1(sK2,X2) = k10_relat_1(k2_funct_1(sK2),X2) | ~v1_relat_1(sK2)) )),
% 1.60/0.58    inference(subsumption_resolution,[],[f114,f66])).
% 1.60/0.58  fof(f114,plain,(
% 1.60/0.58    ( ! [X2] : (k9_relat_1(sK2,X2) = k10_relat_1(k2_funct_1(sK2),X2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 1.60/0.58    inference(resolution,[],[f70,f84])).
% 1.60/0.58  fof(f84,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f43])).
% 1.60/0.58  fof(f43,plain,(
% 1.60/0.58    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.60/0.58    inference(flattening,[],[f42])).
% 1.60/0.58  fof(f42,plain,(
% 1.60/0.58    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.60/0.58    inference(ennf_transformation,[],[f11])).
% 1.60/0.58  fof(f11,axiom,(
% 1.60/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).
% 1.60/0.58  % SZS output end Proof for theBenchmark
% 1.60/0.58  % (22590)------------------------------
% 1.60/0.58  % (22590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.58  % (22590)Termination reason: Refutation
% 1.60/0.58  
% 1.60/0.58  % (22590)Memory used [KB]: 1918
% 1.60/0.58  % (22590)Time elapsed: 0.138 s
% 1.60/0.58  % (22590)------------------------------
% 1.60/0.58  % (22590)------------------------------
% 1.60/0.58  % (22580)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.60/0.58  % (22583)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.60/0.58  % (22571)Success in time 0.22 s
%------------------------------------------------------------------------------
