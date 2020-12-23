%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1021+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:03 EST 2020

% Result     : Theorem 46.92s
% Output     : Refutation 46.92s
% Verified   : 
% Statistics : Number of formulae       :  143 (1444 expanded)
%              Number of leaves         :   18 ( 350 expanded)
%              Depth                    :   29
%              Number of atoms          :  413 (7574 expanded)
%              Number of equality atoms :   91 ( 241 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29700,plain,(
    $false ),
    inference(subsumption_resolution,[],[f29697,f4685])).

fof(f4685,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f1250])).

fof(f1250,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f29697,plain,(
    ~ m1_subset_1(k6_relat_1(sK60),k1_zfmisc_1(k2_zfmisc_1(sK60,sK60))) ),
    inference(trivial_inequality_removal,[],[f29696])).

fof(f29696,plain,
    ( k11_relat_1(k6_relat_1(sK60),sK322(sK60,k6_relat_1(sK60),k6_relat_1(sK60))) != k11_relat_1(k6_relat_1(sK60),sK322(sK60,k6_relat_1(sK60),k6_relat_1(sK60)))
    | ~ m1_subset_1(k6_relat_1(sK60),k1_zfmisc_1(k2_zfmisc_1(sK60,sK60))) ),
    inference(duplicate_literal_removal,[],[f29677])).

fof(f29677,plain,
    ( k11_relat_1(k6_relat_1(sK60),sK322(sK60,k6_relat_1(sK60),k6_relat_1(sK60))) != k11_relat_1(k6_relat_1(sK60),sK322(sK60,k6_relat_1(sK60),k6_relat_1(sK60)))
    | ~ m1_subset_1(k6_relat_1(sK60),k1_zfmisc_1(k2_zfmisc_1(sK60,sK60)))
    | ~ m1_subset_1(k6_relat_1(sK60),k1_zfmisc_1(k2_zfmisc_1(sK60,sK60))) ),
    inference(resolution,[],[f29523,f5986])).

fof(f5986,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X0,X1,X2)
      | k11_relat_1(X1,sK322(X0,X1,X2)) != k11_relat_1(X2,sK322(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f3991])).

fof(f3991,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X0,X1,X2)
          | ( k11_relat_1(X1,sK322(X0,X1,X2)) != k11_relat_1(X2,sK322(X0,X1,X2))
            & r2_hidden(sK322(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK322])],[f2387,f3990])).

fof(f3990,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k11_relat_1(X1,X3) != k11_relat_1(X2,X3)
          & r2_hidden(X3,X0) )
     => ( k11_relat_1(X1,sK322(X0,X1,X2)) != k11_relat_1(X2,sK322(X0,X1,X2))
        & r2_hidden(sK322(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f2387,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X0,X1,X2)
          | ? [X3] :
              ( k11_relat_1(X1,X3) != k11_relat_1(X2,X3)
              & r2_hidden(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(flattening,[],[f2386])).

fof(f2386,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X0,X1,X2)
          | ? [X3] :
              ( k11_relat_1(X1,X3) != k11_relat_1(X2,X3)
              & r2_hidden(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f1268])).

fof(f1268,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
         => ( ! [X3] :
                ( r2_hidden(X3,X0)
               => k11_relat_1(X1,X3) = k11_relat_1(X2,X3) )
           => r2_relset_1(X0,X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relset_1)).

fof(f29523,plain,(
    ~ r2_relset_1(sK60,sK60,k6_relat_1(sK60),k6_relat_1(sK60)) ),
    inference(duplicate_literal_removal,[],[f29512])).

fof(f29512,plain,
    ( ~ r2_relset_1(sK60,sK60,k6_relat_1(sK60),k6_relat_1(sK60))
    | ~ r2_relset_1(sK60,sK60,k6_relat_1(sK60),k6_relat_1(sK60)) ),
    inference(backward_demodulation,[],[f29152,f29511])).

fof(f29511,plain,(
    k6_relat_1(sK60) = k1_partfun1(sK60,sK60,sK60,sK60,k4_relat_1(sK61),sK61) ),
    inference(forward_demodulation,[],[f29510,f11373])).

fof(f11373,plain,(
    k6_relat_1(sK60) = k5_relat_1(k4_relat_1(sK61),sK61) ),
    inference(backward_demodulation,[],[f8234,f11359])).

fof(f11359,plain,(
    sK60 = k2_relat_1(sK61) ),
    inference(backward_demodulation,[],[f8280,f11358])).

fof(f11358,plain,(
    sK60 = k1_relset_1(sK60,sK60,k4_relat_1(sK61)) ),
    inference(subsumption_resolution,[],[f11357,f8225])).

fof(f8225,plain,(
    v1_funct_1(k4_relat_1(sK61)) ),
    inference(backward_demodulation,[],[f8034,f8184])).

fof(f8184,plain,(
    k2_funct_1(sK61) = k4_relat_1(sK61) ),
    inference(subsumption_resolution,[],[f8059,f8093])).

fof(f8093,plain,(
    v1_relat_1(sK61) ),
    inference(resolution,[],[f4600,f6578])).

fof(f6578,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f2748])).

fof(f2748,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f4600,plain,(
    m1_subset_1(sK61,k1_zfmisc_1(k2_zfmisc_1(sK60,sK60))) ),
    inference(cnf_transformation,[],[f3333])).

fof(f3333,plain,
    ( ( ~ r2_relset_1(sK60,sK60,k1_partfun1(sK60,sK60,sK60,sK60,k2_funct_2(sK60,sK61),sK61),k6_partfun1(sK60))
      | ~ r2_relset_1(sK60,sK60,k1_partfun1(sK60,sK60,sK60,sK60,sK61,k2_funct_2(sK60,sK61)),k6_partfun1(sK60)) )
    & m1_subset_1(sK61,k1_zfmisc_1(k2_zfmisc_1(sK60,sK60)))
    & v3_funct_2(sK61,sK60,sK60)
    & v1_funct_2(sK61,sK60,sK60)
    & v1_funct_1(sK61) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK60,sK61])],[f1604,f3332])).

fof(f3332,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ~ r2_relset_1(sK60,sK60,k1_partfun1(sK60,sK60,sK60,sK60,k2_funct_2(sK60,sK61),sK61),k6_partfun1(sK60))
        | ~ r2_relset_1(sK60,sK60,k1_partfun1(sK60,sK60,sK60,sK60,sK61,k2_funct_2(sK60,sK61)),k6_partfun1(sK60)) )
      & m1_subset_1(sK61,k1_zfmisc_1(k2_zfmisc_1(sK60,sK60)))
      & v3_funct_2(sK61,sK60,sK60)
      & v1_funct_2(sK61,sK60,sK60)
      & v1_funct_1(sK61) ) ),
    introduced(choice_axiom,[])).

fof(f1604,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f1603])).

fof(f1603,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f1565])).

fof(f1565,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f1564])).

fof(f1564,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

fof(f8059,plain,
    ( k2_funct_1(sK61) = k4_relat_1(sK61)
    | ~ v1_relat_1(sK61) ),
    inference(subsumption_resolution,[],[f8042,f4597])).

fof(f4597,plain,(
    v1_funct_1(sK61) ),
    inference(cnf_transformation,[],[f3333])).

fof(f8042,plain,
    ( k2_funct_1(sK61) = k4_relat_1(sK61)
    | ~ v1_funct_1(sK61)
    | ~ v1_relat_1(sK61) ),
    inference(resolution,[],[f8038,f5162])).

fof(f5162,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1921])).

fof(f1921,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1920])).

fof(f1920,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f906])).

fof(f906,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f8038,plain,(
    v2_funct_1(sK61) ),
    inference(subsumption_resolution,[],[f8037,f4600])).

fof(f8037,plain,
    ( v2_funct_1(sK61)
    | ~ m1_subset_1(sK61,k1_zfmisc_1(k2_zfmisc_1(sK60,sK60))) ),
    inference(subsumption_resolution,[],[f8023,f4597])).

fof(f8023,plain,
    ( v2_funct_1(sK61)
    | ~ v1_funct_1(sK61)
    | ~ m1_subset_1(sK61,k1_zfmisc_1(k2_zfmisc_1(sK60,sK60))) ),
    inference(resolution,[],[f4599,f6612])).

fof(f6612,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_funct_2(X2,X0,X1)
      | v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2773])).

fof(f2773,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f2772])).

fof(f2772,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1470])).

fof(f1470,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f4599,plain,(
    v3_funct_2(sK61,sK60,sK60) ),
    inference(cnf_transformation,[],[f3333])).

fof(f8034,plain,(
    v1_funct_1(k2_funct_1(sK61)) ),
    inference(backward_demodulation,[],[f8026,f8032])).

fof(f8032,plain,(
    k2_funct_2(sK60,sK61) = k2_funct_1(sK61) ),
    inference(subsumption_resolution,[],[f8031,f4597])).

fof(f8031,plain,
    ( k2_funct_2(sK60,sK61) = k2_funct_1(sK61)
    | ~ v1_funct_1(sK61) ),
    inference(subsumption_resolution,[],[f8030,f4598])).

fof(f4598,plain,(
    v1_funct_2(sK61,sK60,sK60) ),
    inference(cnf_transformation,[],[f3333])).

fof(f8030,plain,
    ( k2_funct_2(sK60,sK61) = k2_funct_1(sK61)
    | ~ v1_funct_2(sK61,sK60,sK60)
    | ~ v1_funct_1(sK61) ),
    inference(subsumption_resolution,[],[f8022,f4600])).

fof(f8022,plain,
    ( ~ m1_subset_1(sK61,k1_zfmisc_1(k2_zfmisc_1(sK60,sK60)))
    | k2_funct_2(sK60,sK61) = k2_funct_1(sK61)
    | ~ v1_funct_2(sK61,sK60,sK60)
    | ~ v1_funct_1(sK61) ),
    inference(resolution,[],[f4599,f6049])).

fof(f6049,plain,(
    ! [X0,X1] :
      ( ~ v3_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f2433])).

fof(f2433,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f2432])).

fof(f2432,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f1503])).

fof(f1503,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f8026,plain,(
    v1_funct_1(k2_funct_2(sK60,sK61)) ),
    inference(subsumption_resolution,[],[f8025,f4597])).

fof(f8025,plain,
    ( v1_funct_1(k2_funct_2(sK60,sK61))
    | ~ v1_funct_1(sK61) ),
    inference(subsumption_resolution,[],[f8024,f4598])).

fof(f8024,plain,
    ( v1_funct_1(k2_funct_2(sK60,sK61))
    | ~ v1_funct_2(sK61,sK60,sK60)
    | ~ v1_funct_1(sK61) ),
    inference(subsumption_resolution,[],[f8020,f4600])).

fof(f8020,plain,
    ( ~ m1_subset_1(sK61,k1_zfmisc_1(k2_zfmisc_1(sK60,sK60)))
    | v1_funct_1(k2_funct_2(sK60,sK61))
    | ~ v1_funct_2(sK61,sK60,sK60)
    | ~ v1_funct_1(sK61) ),
    inference(resolution,[],[f4599,f6050])).

fof(f6050,plain,(
    ! [X0,X1] :
      ( ~ v3_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | v1_funct_1(k2_funct_2(X0,X1))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f2435])).

fof(f2435,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f2434])).

fof(f2434,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f1480])).

fof(f1480,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(f11357,plain,
    ( sK60 = k1_relset_1(sK60,sK60,k4_relat_1(sK61))
    | ~ v1_funct_1(k4_relat_1(sK61)) ),
    inference(subsumption_resolution,[],[f11331,f8224])).

fof(f8224,plain,(
    m1_subset_1(k4_relat_1(sK61),k1_zfmisc_1(k2_zfmisc_1(sK60,sK60))) ),
    inference(backward_demodulation,[],[f8033,f8184])).

fof(f8033,plain,(
    m1_subset_1(k2_funct_1(sK61),k1_zfmisc_1(k2_zfmisc_1(sK60,sK60))) ),
    inference(backward_demodulation,[],[f8029,f8032])).

fof(f8029,plain,(
    m1_subset_1(k2_funct_2(sK60,sK61),k1_zfmisc_1(k2_zfmisc_1(sK60,sK60))) ),
    inference(subsumption_resolution,[],[f8028,f4597])).

fof(f8028,plain,
    ( m1_subset_1(k2_funct_2(sK60,sK61),k1_zfmisc_1(k2_zfmisc_1(sK60,sK60)))
    | ~ v1_funct_1(sK61) ),
    inference(subsumption_resolution,[],[f8027,f4598])).

fof(f8027,plain,
    ( m1_subset_1(k2_funct_2(sK60,sK61),k1_zfmisc_1(k2_zfmisc_1(sK60,sK60)))
    | ~ v1_funct_2(sK61,sK60,sK60)
    | ~ v1_funct_1(sK61) ),
    inference(subsumption_resolution,[],[f8021,f4600])).

fof(f8021,plain,
    ( ~ m1_subset_1(sK61,k1_zfmisc_1(k2_zfmisc_1(sK60,sK60)))
    | m1_subset_1(k2_funct_2(sK60,sK61),k1_zfmisc_1(k2_zfmisc_1(sK60,sK60)))
    | ~ v1_funct_2(sK61,sK60,sK60)
    | ~ v1_funct_1(sK61) ),
    inference(resolution,[],[f4599,f6053])).

fof(f6053,plain,(
    ! [X0,X1] :
      ( ~ v3_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f2435])).

fof(f11331,plain,
    ( ~ m1_subset_1(k4_relat_1(sK61),k1_zfmisc_1(k2_zfmisc_1(sK60,sK60)))
    | sK60 = k1_relset_1(sK60,sK60,k4_relat_1(sK61))
    | ~ v1_funct_1(k4_relat_1(sK61)) ),
    inference(resolution,[],[f9460,f6057])).

fof(f6057,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relset_1(X0,X0,X1) = X0
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f2443])).

fof(f2443,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f2442])).

fof(f2442,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f1553])).

fof(f1553,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

fof(f9460,plain,(
    v1_funct_2(k4_relat_1(sK61),sK60,sK60) ),
    inference(subsumption_resolution,[],[f9459,f4597])).

fof(f9459,plain,
    ( v1_funct_2(k4_relat_1(sK61),sK60,sK60)
    | ~ v1_funct_1(sK61) ),
    inference(subsumption_resolution,[],[f9458,f4598])).

fof(f9458,plain,
    ( v1_funct_2(k4_relat_1(sK61),sK60,sK60)
    | ~ v1_funct_2(sK61,sK60,sK60)
    | ~ v1_funct_1(sK61) ),
    inference(subsumption_resolution,[],[f9457,f4599])).

fof(f9457,plain,
    ( v1_funct_2(k4_relat_1(sK61),sK60,sK60)
    | ~ v3_funct_2(sK61,sK60,sK60)
    | ~ v1_funct_2(sK61,sK60,sK60)
    | ~ v1_funct_1(sK61) ),
    inference(subsumption_resolution,[],[f9450,f4600])).

fof(f9450,plain,
    ( v1_funct_2(k4_relat_1(sK61),sK60,sK60)
    | ~ m1_subset_1(sK61,k1_zfmisc_1(k2_zfmisc_1(sK60,sK60)))
    | ~ v3_funct_2(sK61,sK60,sK60)
    | ~ v1_funct_2(sK61,sK60,sK60)
    | ~ v1_funct_1(sK61) ),
    inference(superposition,[],[f6051,f8223])).

fof(f8223,plain,(
    k2_funct_2(sK60,sK61) = k4_relat_1(sK61) ),
    inference(backward_demodulation,[],[f8032,f8184])).

fof(f6051,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f2435])).

fof(f8280,plain,(
    k2_relat_1(sK61) = k1_relset_1(sK60,sK60,k4_relat_1(sK61)) ),
    inference(forward_demodulation,[],[f8279,f8094])).

fof(f8094,plain,(
    k2_relset_1(sK60,sK60,sK61) = k2_relat_1(sK61) ),
    inference(resolution,[],[f4600,f6580])).

fof(f6580,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2750])).

fof(f2750,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1228])).

fof(f1228,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f8279,plain,(
    k2_relset_1(sK60,sK60,sK61) = k1_relset_1(sK60,sK60,k4_relat_1(sK61)) ),
    inference(forward_demodulation,[],[f8100,f8096])).

fof(f8096,plain,(
    k4_relat_1(sK61) = k3_relset_1(sK60,sK60,sK61) ),
    inference(resolution,[],[f4600,f6582])).

fof(f6582,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f2752])).

fof(f2752,plain,(
    ! [X0,X1,X2] :
      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1229])).

fof(f1229,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

fof(f8100,plain,(
    k2_relset_1(sK60,sK60,sK61) = k1_relset_1(sK60,sK60,k3_relset_1(sK60,sK60,sK61)) ),
    inference(resolution,[],[f4600,f6591])).

fof(f6591,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f2759])).

fof(f2759,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
        & k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1247])).

fof(f1247,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
        & k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relset_1)).

fof(f8234,plain,(
    k6_relat_1(k2_relat_1(sK61)) = k5_relat_1(k4_relat_1(sK61),sK61) ),
    inference(backward_demodulation,[],[f8193,f8184])).

fof(f8193,plain,(
    k5_relat_1(k2_funct_1(sK61),sK61) = k6_relat_1(k2_relat_1(sK61)) ),
    inference(subsumption_resolution,[],[f8068,f8093])).

fof(f8068,plain,
    ( k5_relat_1(k2_funct_1(sK61),sK61) = k6_relat_1(k2_relat_1(sK61))
    | ~ v1_relat_1(sK61) ),
    inference(subsumption_resolution,[],[f8051,f4597])).

fof(f8051,plain,
    ( k5_relat_1(k2_funct_1(sK61),sK61) = k6_relat_1(k2_relat_1(sK61))
    | ~ v1_funct_1(sK61)
    | ~ v1_relat_1(sK61) ),
    inference(resolution,[],[f8038,f5171])).

fof(f5171,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1931])).

fof(f1931,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1930])).

fof(f1930,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1032])).

fof(f1032,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f29510,plain,(
    k1_partfun1(sK60,sK60,sK60,sK60,k4_relat_1(sK61),sK61) = k5_relat_1(k4_relat_1(sK61),sK61) ),
    inference(subsumption_resolution,[],[f29391,f8225])).

fof(f29391,plain,
    ( k1_partfun1(sK60,sK60,sK60,sK60,k4_relat_1(sK61),sK61) = k5_relat_1(k4_relat_1(sK61),sK61)
    | ~ v1_funct_1(k4_relat_1(sK61)) ),
    inference(resolution,[],[f8301,f8224])).

fof(f8301,plain,(
    ! [X14,X12,X13] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | k5_relat_1(X12,sK61) = k1_partfun1(X13,X14,sK60,sK60,X12,sK61)
      | ~ v1_funct_1(X12) ) ),
    inference(subsumption_resolution,[],[f8116,f4597])).

fof(f8116,plain,(
    ! [X14,X12,X13] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | ~ v1_funct_1(sK61)
      | k5_relat_1(X12,sK61) = k1_partfun1(X13,X14,sK60,sK60,X12,sK61)
      | ~ v1_funct_1(X12) ) ),
    inference(resolution,[],[f4600,f7382])).

fof(f7382,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f3203])).

fof(f3203,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f3202])).

fof(f3202,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f1502])).

fof(f1502,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f29152,plain,
    ( ~ r2_relset_1(sK60,sK60,k1_partfun1(sK60,sK60,sK60,sK60,k4_relat_1(sK61),sK61),k6_relat_1(sK60))
    | ~ r2_relset_1(sK60,sK60,k6_relat_1(sK60),k6_relat_1(sK60)) ),
    inference(backward_demodulation,[],[f8246,f29151])).

fof(f29151,plain,(
    k6_relat_1(sK60) = k1_partfun1(sK60,sK60,sK60,sK60,sK61,k4_relat_1(sK61)) ),
    inference(forward_demodulation,[],[f29150,f8273])).

fof(f8273,plain,(
    k6_relat_1(sK60) = k5_relat_1(sK61,k4_relat_1(sK61)) ),
    inference(backward_demodulation,[],[f8233,f8269])).

fof(f8269,plain,(
    sK60 = k1_relat_1(sK61) ),
    inference(forward_demodulation,[],[f8095,f7975])).

fof(f7975,plain,(
    sK60 = k1_relset_1(sK60,sK60,sK61) ),
    inference(subsumption_resolution,[],[f7974,f4597])).

fof(f7974,plain,
    ( sK60 = k1_relset_1(sK60,sK60,sK61)
    | ~ v1_funct_1(sK61) ),
    inference(subsumption_resolution,[],[f7942,f4600])).

fof(f7942,plain,
    ( ~ m1_subset_1(sK61,k1_zfmisc_1(k2_zfmisc_1(sK60,sK60)))
    | sK60 = k1_relset_1(sK60,sK60,sK61)
    | ~ v1_funct_1(sK61) ),
    inference(resolution,[],[f4598,f6057])).

fof(f8095,plain,(
    k1_relat_1(sK61) = k1_relset_1(sK60,sK60,sK61) ),
    inference(resolution,[],[f4600,f6581])).

fof(f6581,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2751])).

fof(f2751,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1227])).

fof(f1227,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f8233,plain,(
    k6_relat_1(k1_relat_1(sK61)) = k5_relat_1(sK61,k4_relat_1(sK61)) ),
    inference(backward_demodulation,[],[f8192,f8184])).

fof(f8192,plain,(
    k5_relat_1(sK61,k2_funct_1(sK61)) = k6_relat_1(k1_relat_1(sK61)) ),
    inference(subsumption_resolution,[],[f8067,f8093])).

fof(f8067,plain,
    ( k5_relat_1(sK61,k2_funct_1(sK61)) = k6_relat_1(k1_relat_1(sK61))
    | ~ v1_relat_1(sK61) ),
    inference(subsumption_resolution,[],[f8050,f4597])).

fof(f8050,plain,
    ( k5_relat_1(sK61,k2_funct_1(sK61)) = k6_relat_1(k1_relat_1(sK61))
    | ~ v1_funct_1(sK61)
    | ~ v1_relat_1(sK61) ),
    inference(resolution,[],[f8038,f5170])).

fof(f5170,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1931])).

fof(f29150,plain,(
    k5_relat_1(sK61,k4_relat_1(sK61)) = k1_partfun1(sK60,sK60,sK60,sK60,sK61,k4_relat_1(sK61)) ),
    inference(subsumption_resolution,[],[f29029,f8225])).

fof(f29029,plain,
    ( ~ v1_funct_1(k4_relat_1(sK61))
    | k5_relat_1(sK61,k4_relat_1(sK61)) = k1_partfun1(sK60,sK60,sK60,sK60,sK61,k4_relat_1(sK61)) ),
    inference(resolution,[],[f8300,f8224])).

fof(f8300,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | ~ v1_funct_1(X9)
      | k5_relat_1(sK61,X9) = k1_partfun1(sK60,sK60,X10,X11,sK61,X9) ) ),
    inference(subsumption_resolution,[],[f8115,f4597])).

fof(f8115,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | ~ v1_funct_1(X9)
      | k5_relat_1(sK61,X9) = k1_partfun1(sK60,sK60,X10,X11,sK61,X9)
      | ~ v1_funct_1(sK61) ) ),
    inference(resolution,[],[f4600,f7382])).

fof(f8246,plain,
    ( ~ r2_relset_1(sK60,sK60,k1_partfun1(sK60,sK60,sK60,sK60,k4_relat_1(sK61),sK61),k6_relat_1(sK60))
    | ~ r2_relset_1(sK60,sK60,k1_partfun1(sK60,sK60,sK60,sK60,sK61,k4_relat_1(sK61)),k6_relat_1(sK60)) ),
    inference(forward_demodulation,[],[f8226,f8184])).

fof(f8226,plain,
    ( ~ r2_relset_1(sK60,sK60,k1_partfun1(sK60,sK60,sK60,sK60,k4_relat_1(sK61),sK61),k6_relat_1(sK60))
    | ~ r2_relset_1(sK60,sK60,k1_partfun1(sK60,sK60,sK60,sK60,sK61,k2_funct_1(sK61)),k6_relat_1(sK60)) ),
    inference(backward_demodulation,[],[f8036,f8184])).

fof(f8036,plain,
    ( ~ r2_relset_1(sK60,sK60,k1_partfun1(sK60,sK60,sK60,sK60,sK61,k2_funct_1(sK61)),k6_relat_1(sK60))
    | ~ r2_relset_1(sK60,sK60,k1_partfun1(sK60,sK60,sK60,sK60,k2_funct_1(sK61),sK61),k6_relat_1(sK60)) ),
    inference(forward_demodulation,[],[f8035,f8032])).

fof(f8035,plain,
    ( ~ r2_relset_1(sK60,sK60,k1_partfun1(sK60,sK60,sK60,sK60,k2_funct_1(sK61),sK61),k6_relat_1(sK60))
    | ~ r2_relset_1(sK60,sK60,k1_partfun1(sK60,sK60,sK60,sK60,sK61,k2_funct_2(sK60,sK61)),k6_relat_1(sK60)) ),
    inference(backward_demodulation,[],[f7923,f8032])).

fof(f7923,plain,
    ( ~ r2_relset_1(sK60,sK60,k1_partfun1(sK60,sK60,sK60,sK60,sK61,k2_funct_2(sK60,sK61)),k6_relat_1(sK60))
    | ~ r2_relset_1(sK60,sK60,k1_partfun1(sK60,sK60,sK60,sK60,k2_funct_2(sK60,sK61),sK61),k6_relat_1(sK60)) ),
    inference(forward_demodulation,[],[f7922,f4654])).

fof(f4654,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f1505])).

fof(f1505,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f7922,plain,
    ( ~ r2_relset_1(sK60,sK60,k1_partfun1(sK60,sK60,sK60,sK60,k2_funct_2(sK60,sK61),sK61),k6_relat_1(sK60))
    | ~ r2_relset_1(sK60,sK60,k1_partfun1(sK60,sK60,sK60,sK60,sK61,k2_funct_2(sK60,sK61)),k6_partfun1(sK60)) ),
    inference(forward_demodulation,[],[f4601,f4654])).

fof(f4601,plain,
    ( ~ r2_relset_1(sK60,sK60,k1_partfun1(sK60,sK60,sK60,sK60,k2_funct_2(sK60,sK61),sK61),k6_partfun1(sK60))
    | ~ r2_relset_1(sK60,sK60,k1_partfun1(sK60,sK60,sK60,sK60,sK61,k2_funct_2(sK60,sK61)),k6_partfun1(sK60)) ),
    inference(cnf_transformation,[],[f3333])).
%------------------------------------------------------------------------------
