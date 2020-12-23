%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:30 EST 2020

% Result     : Theorem 1.75s
% Output     : Refutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :  183 (1108473 expanded)
%              Number of leaves         :   20 (374876 expanded)
%              Depth                    :   38
%              Number of atoms          :  550 (7646210 expanded)
%              Number of equality atoms :  150 (1142791 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1816,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1788,f1637])).

fof(f1637,plain,(
    r2_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f1075,f1625])).

fof(f1625,plain,(
    k1_xboole_0 = k2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1614,f1075])).

fof(f1614,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(superposition,[],[f1087,f1141])).

fof(f1141,plain,
    ( k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0))
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(backward_demodulation,[],[f978,f1041])).

fof(f1041,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f1037,f681])).

fof(f681,plain,
    ( r2_funct_2(k1_xboole_0,k1_xboole_0,sK2,sK2)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f526,f663])).

fof(f663,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f647,f522])).

fof(f522,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f155,f516])).

fof(f516,plain,(
    k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f506,f308])).

fof(f308,plain,(
    r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) ),
    inference(unit_resulting_resolution,[],[f59,f59,f258,f258,f259,f259,f100])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

fof(f259,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    inference(unit_resulting_resolution,[],[f145,f59,f233,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f233,plain,(
    r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f145,f157,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f157,plain,(
    v5_relat_1(sK2,k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f137,f151])).

fof(f151,plain,(
    k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f115,f136])).

fof(f136,plain,(
    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f116,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f116,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f109,f112])).

fof(f112,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unit_resulting_resolution,[],[f58,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f58,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f51,f50,f49])).

fof(f49,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
                & v2_funct_1(X2)
                & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2)
            & v2_funct_1(X2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1) )
   => ( ? [X2] :
          ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2)
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X2] :
        ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2)
        & v2_funct_1(X2)
        & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
      & v2_funct_1(sK2)
      & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                 => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,negated_conjecture,(
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
                 => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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
               => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).

fof(f109,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f61,f106])).

fof(f106,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f57,f65])).

fof(f57,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f61,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f52])).

fof(f115,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f110,f112])).

fof(f110,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f62,f106])).

fof(f62,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f137,plain,(
    v5_relat_1(sK2,k2_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f116,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f145,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f73,f116,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f73,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f258,plain,(
    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f145,f59,f233,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f506,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f326,f505])).

fof(f505,plain,(
    sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f498,f180])).

fof(f180,plain,(
    sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f63,f59,f145,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(f63,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f498,plain,(
    k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f178,f179,f379,f380,f440,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f440,plain,(
    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f425,f182])).

fof(f182,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f63,f59,f145,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f425,plain,(
    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f380,f85])).

fof(f380,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    inference(unit_resulting_resolution,[],[f59,f63,f258,f259,f300,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f300,plain,(
    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f259,f85])).

fof(f379,plain,(
    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f59,f63,f258,f259,f300,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_2(k2_funct_1(X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f179,plain,(
    v2_funct_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f63,f59,f145,f69])).

fof(f69,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f178,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f63,f59,f145,f68])).

fof(f68,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f326,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(superposition,[],[f274,f168])).

fof(f168,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f167,f163])).

fof(f163,plain,(
    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(forward_demodulation,[],[f135,f151])).

fof(f135,plain,(
    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(unit_resulting_resolution,[],[f116,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f167,plain,
    ( k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f166,f151])).

fof(f166,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(forward_demodulation,[],[f165,f151])).

fof(f165,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f164,f155])).

fof(f164,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | k1_xboole_0 = k2_struct_0(sK1)
    | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(forward_demodulation,[],[f146,f151])).

fof(f146,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k1_xboole_0 = k2_struct_0(sK1)
    | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(resolution,[],[f116,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f274,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),sK2) ),
    inference(backward_demodulation,[],[f153,f270])).

fof(f270,plain,(
    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f59,f63,f155,f154,f156,f99])).

fof(f156,plain,(
    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(backward_demodulation,[],[f136,f151])).

fof(f154,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f116,f151])).

fof(f153,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2) ),
    inference(backward_demodulation,[],[f114,f151])).

fof(f114,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) ),
    inference(backward_demodulation,[],[f111,f112])).

fof(f111,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(backward_demodulation,[],[f64,f106])).

fof(f64,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f155,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f117,f151])).

fof(f117,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f108,f112])).

fof(f108,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f60,f106])).

fof(f60,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f52])).

fof(f647,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0)
    | k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f521,f103])).

fof(f103,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f521,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) ),
    inference(backward_demodulation,[],[f154,f516])).

fof(f526,plain,(
    r2_funct_2(k2_struct_0(sK0),k1_xboole_0,sK2,sK2) ),
    inference(backward_demodulation,[],[f162,f516])).

fof(f162,plain,(
    r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2) ),
    inference(backward_demodulation,[],[f144,f151])).

fof(f144,plain,(
    r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) ),
    inference(unit_resulting_resolution,[],[f59,f59,f117,f117,f116,f116,f100])).

fof(f1037,plain,
    ( ~ r2_funct_2(k1_xboole_0,k1_xboole_0,sK2,sK2)
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f1034])).

fof(f1034,plain,
    ( ~ r2_funct_2(k1_xboole_0,k1_xboole_0,sK2,sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f683,f862])).

fof(f862,plain,
    ( sK2 = k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f581,f598])).

fof(f598,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f575,f533])).

fof(f533,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f233,f516])).

fof(f575,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(backward_demodulation,[],[f487,f516])).

fof(f487,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f480,f330])).

fof(f330,plain,(
    ! [X0] :
      ( v1_funct_2(sK2,k1_relat_1(sK2),X0)
      | ~ r1_tarski(k2_relat_1(sK2),X0) ) ),
    inference(resolution,[],[f121,f145])).

fof(f121,plain,(
    ! [X7] :
      ( ~ v1_relat_1(sK2)
      | v1_funct_2(sK2,k1_relat_1(sK2),X7)
      | ~ r1_tarski(k2_relat_1(sK2),X7) ) ),
    inference(resolution,[],[f59,f77])).

fof(f480,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k1_xboole_0)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f357,f103])).

fof(f357,plain,(
    ! [X0] :
      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0)))
      | ~ r1_tarski(k2_relat_1(sK2),X0) ) ),
    inference(resolution,[],[f122,f145])).

fof(f122,plain,(
    ! [X8] :
      ( ~ v1_relat_1(sK2)
      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X8)))
      | ~ r1_tarski(k2_relat_1(sK2),X8) ) ),
    inference(resolution,[],[f59,f78])).

fof(f581,plain,(
    sK2 = k2_tops_2(k1_xboole_0,k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f505,f516])).

fof(f683,plain,
    ( ~ r2_funct_2(k1_xboole_0,k1_xboole_0,k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)),sK2)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f539,f663])).

fof(f539,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),sK2) ),
    inference(backward_demodulation,[],[f274,f516])).

fof(f978,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f971,f546])).

fof(f546,plain,(
    v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f335,f516])).

fof(f335,plain,(
    v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f178,f272,f273,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f273,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f59,f63,f155,f154,f156,f98])).

fof(f272,plain,(
    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f59,f63,f155,f154,f156,f97])).

fof(f971,plain,
    ( ~ v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0)
    | k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(resolution,[],[f547,f103])).

fof(f547,plain,(
    m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) ),
    inference(backward_demodulation,[],[f336,f516])).

fof(f336,plain,(
    m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    inference(unit_resulting_resolution,[],[f178,f272,f273,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f1087,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k1_xboole_0) ),
    inference(backward_demodulation,[],[f539,f1041])).

fof(f1075,plain,(
    r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f526,f1041])).

fof(f1788,plain,(
    ~ r2_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f1642,f1758])).

fof(f1758,plain,(
    k1_xboole_0 = k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f1116,f1738])).

fof(f1738,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f1638,f1706])).

fof(f1706,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f1635,f1634,f105])).

fof(f105,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f1634,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f1071,f1625])).

fof(f1071,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) ),
    inference(backward_demodulation,[],[f521,f1041])).

fof(f1635,plain,(
    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f1072,f1625])).

fof(f1072,plain,(
    v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f522,f1041])).

fof(f1638,plain,(
    k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f1076,f1625])).

fof(f1076,plain,(
    k1_relat_1(k1_xboole_0) = k1_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f527,f1041])).

fof(f527,plain,(
    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f163,f516])).

fof(f1116,plain,(
    k1_xboole_0 = k2_tops_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k2_funct_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f581,f1041])).

fof(f1642,plain,(
    ~ r2_funct_2(k1_xboole_0,k1_xboole_0,k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)),k1_xboole_0) ),
    inference(backward_demodulation,[],[f1087,f1625])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:47:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (26829)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % (26834)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.49  % (26838)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.49  % (26830)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.49  % (26828)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (26827)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.49  % (26824)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (26832)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.50  % (26831)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.50  % (26837)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.50  % (26825)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.50  % (26823)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (26833)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.51  % (26843)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.51  % (26840)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.51  % (26843)Refutation not found, incomplete strategy% (26843)------------------------------
% 0.20/0.51  % (26843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (26843)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (26843)Memory used [KB]: 10618
% 0.20/0.51  % (26843)Time elapsed: 0.104 s
% 0.20/0.51  % (26843)------------------------------
% 0.20/0.51  % (26843)------------------------------
% 0.20/0.51  % (26842)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.52  % (26826)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (26836)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.52  % (26839)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.53  % (26841)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.53  % (26835)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.59/0.56  % (26824)Refutation not found, incomplete strategy% (26824)------------------------------
% 1.59/0.56  % (26824)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.56  % (26824)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.56  
% 1.59/0.56  % (26824)Memory used [KB]: 11257
% 1.59/0.56  % (26824)Time elapsed: 0.155 s
% 1.59/0.56  % (26824)------------------------------
% 1.59/0.56  % (26824)------------------------------
% 1.59/0.57  % (26836)Refutation not found, incomplete strategy% (26836)------------------------------
% 1.59/0.57  % (26836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.57  % (26836)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.57  
% 1.59/0.57  % (26836)Memory used [KB]: 1918
% 1.59/0.57  % (26836)Time elapsed: 0.149 s
% 1.59/0.57  % (26836)------------------------------
% 1.59/0.57  % (26836)------------------------------
% 1.75/0.58  % (26838)Refutation found. Thanks to Tanya!
% 1.75/0.58  % SZS status Theorem for theBenchmark
% 1.75/0.58  % SZS output start Proof for theBenchmark
% 1.75/0.58  fof(f1816,plain,(
% 1.75/0.58    $false),
% 1.75/0.58    inference(subsumption_resolution,[],[f1788,f1637])).
% 1.75/0.58  fof(f1637,plain,(
% 1.75/0.58    r2_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.75/0.58    inference(backward_demodulation,[],[f1075,f1625])).
% 1.75/0.58  fof(f1625,plain,(
% 1.75/0.58    k1_xboole_0 = k2_struct_0(sK0)),
% 1.75/0.58    inference(subsumption_resolution,[],[f1614,f1075])).
% 1.75/0.58  fof(f1614,plain,(
% 1.75/0.58    ~r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k2_struct_0(sK0)),
% 1.75/0.58    inference(superposition,[],[f1087,f1141])).
% 1.75/0.58  fof(f1141,plain,(
% 1.75/0.58    k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) | k1_xboole_0 = k2_struct_0(sK0)),
% 1.75/0.58    inference(backward_demodulation,[],[f978,f1041])).
% 1.75/0.58  fof(f1041,plain,(
% 1.75/0.58    k1_xboole_0 = sK2),
% 1.75/0.58    inference(subsumption_resolution,[],[f1037,f681])).
% 1.75/0.58  fof(f681,plain,(
% 1.75/0.58    r2_funct_2(k1_xboole_0,k1_xboole_0,sK2,sK2) | k1_xboole_0 = sK2),
% 1.75/0.58    inference(superposition,[],[f526,f663])).
% 1.75/0.58  fof(f663,plain,(
% 1.75/0.58    k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 = sK2),
% 1.75/0.58    inference(subsumption_resolution,[],[f647,f522])).
% 1.75/0.58  fof(f522,plain,(
% 1.75/0.58    v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0)),
% 1.75/0.58    inference(backward_demodulation,[],[f155,f516])).
% 1.75/0.58  fof(f516,plain,(
% 1.75/0.58    k1_xboole_0 = k2_relat_1(sK2)),
% 1.75/0.58    inference(subsumption_resolution,[],[f506,f308])).
% 1.75/0.58  fof(f308,plain,(
% 1.75/0.58    r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)),
% 1.75/0.58    inference(unit_resulting_resolution,[],[f59,f59,f258,f258,f259,f259,f100])).
% 1.75/0.58  fof(f100,plain,(
% 1.75/0.58    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.75/0.58    inference(cnf_transformation,[],[f48])).
% 1.75/0.58  fof(f48,plain,(
% 1.75/0.58    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.75/0.58    inference(flattening,[],[f47])).
% 1.75/0.58  fof(f47,plain,(
% 1.75/0.58    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.75/0.58    inference(ennf_transformation,[],[f12])).
% 1.75/0.58  fof(f12,axiom,(
% 1.75/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 1.75/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).
% 1.75/0.58  fof(f259,plain,(
% 1.75/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 1.75/0.58    inference(unit_resulting_resolution,[],[f145,f59,f233,f78])).
% 1.75/0.58  fof(f78,plain,(
% 1.75/0.58    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 1.75/0.58    inference(cnf_transformation,[],[f35])).
% 1.75/0.58  fof(f35,plain,(
% 1.75/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.75/0.58    inference(flattening,[],[f34])).
% 1.75/0.58  fof(f34,plain,(
% 1.75/0.58    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.75/0.58    inference(ennf_transformation,[],[f14])).
% 1.75/0.58  fof(f14,axiom,(
% 1.75/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.75/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 1.75/0.58  fof(f233,plain,(
% 1.75/0.58    r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2))),
% 1.75/0.58    inference(unit_resulting_resolution,[],[f145,f157,f74])).
% 1.75/0.58  fof(f74,plain,(
% 1.75/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0)) )),
% 1.75/0.58    inference(cnf_transformation,[],[f53])).
% 1.75/0.58  fof(f53,plain,(
% 1.75/0.58    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.75/0.58    inference(nnf_transformation,[],[f33])).
% 1.75/0.58  fof(f33,plain,(
% 1.75/0.58    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.75/0.58    inference(ennf_transformation,[],[f2])).
% 1.75/0.58  fof(f2,axiom,(
% 1.75/0.58    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.75/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.75/0.58  fof(f157,plain,(
% 1.75/0.58    v5_relat_1(sK2,k2_relat_1(sK2))),
% 1.75/0.58    inference(backward_demodulation,[],[f137,f151])).
% 1.75/0.58  fof(f151,plain,(
% 1.75/0.58    k2_struct_0(sK1) = k2_relat_1(sK2)),
% 1.75/0.58    inference(backward_demodulation,[],[f115,f136])).
% 1.75/0.58  fof(f136,plain,(
% 1.75/0.58    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)),
% 1.75/0.58    inference(unit_resulting_resolution,[],[f116,f85])).
% 1.75/0.58  fof(f85,plain,(
% 1.75/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.75/0.58    inference(cnf_transformation,[],[f37])).
% 1.75/0.58  fof(f37,plain,(
% 1.75/0.58    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.58    inference(ennf_transformation,[],[f9])).
% 1.75/0.58  fof(f9,axiom,(
% 1.75/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.75/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.75/0.58  fof(f116,plain,(
% 1.75/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 1.75/0.58    inference(backward_demodulation,[],[f109,f112])).
% 1.75/0.58  fof(f112,plain,(
% 1.75/0.58    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 1.75/0.58    inference(unit_resulting_resolution,[],[f58,f65])).
% 1.75/0.58  fof(f65,plain,(
% 1.75/0.58    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.75/0.58    inference(cnf_transformation,[],[f25])).
% 1.75/0.58  fof(f25,plain,(
% 1.75/0.58    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.75/0.58    inference(ennf_transformation,[],[f15])).
% 1.75/0.58  fof(f15,axiom,(
% 1.75/0.58    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.75/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.75/0.58  fof(f58,plain,(
% 1.75/0.58    l1_struct_0(sK1)),
% 1.75/0.58    inference(cnf_transformation,[],[f52])).
% 1.75/0.58  fof(f52,plain,(
% 1.75/0.58    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 1.75/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f51,f50,f49])).
% 1.75/0.58  fof(f49,plain,(
% 1.75/0.58    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 1.75/0.58    introduced(choice_axiom,[])).
% 1.75/0.58  fof(f50,plain,(
% 1.75/0.58    ? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))),
% 1.75/0.58    introduced(choice_axiom,[])).
% 1.75/0.58  fof(f51,plain,(
% 1.75/0.58    ? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 1.75/0.58    introduced(choice_axiom,[])).
% 1.75/0.58  fof(f24,plain,(
% 1.75/0.58    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 1.75/0.58    inference(flattening,[],[f23])).
% 1.75/0.58  fof(f23,plain,(
% 1.75/0.58    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 1.75/0.58    inference(ennf_transformation,[],[f20])).
% 1.75/0.58  fof(f20,plain,(
% 1.75/0.58    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 1.75/0.58    inference(pure_predicate_removal,[],[f19])).
% 1.75/0.58  fof(f19,negated_conjecture,(
% 1.75/0.58    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 1.75/0.58    inference(negated_conjecture,[],[f18])).
% 1.75/0.58  fof(f18,conjecture,(
% 1.75/0.58    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 1.75/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).
% 1.75/0.58  fof(f109,plain,(
% 1.75/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1))))),
% 1.75/0.58    inference(backward_demodulation,[],[f61,f106])).
% 1.75/0.58  fof(f106,plain,(
% 1.75/0.58    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.75/0.58    inference(unit_resulting_resolution,[],[f57,f65])).
% 1.75/0.58  fof(f57,plain,(
% 1.75/0.58    l1_struct_0(sK0)),
% 1.75/0.58    inference(cnf_transformation,[],[f52])).
% 1.75/0.58  fof(f61,plain,(
% 1.75/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.75/0.58    inference(cnf_transformation,[],[f52])).
% 1.75/0.58  fof(f115,plain,(
% 1.75/0.58    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.75/0.58    inference(backward_demodulation,[],[f110,f112])).
% 1.75/0.58  fof(f110,plain,(
% 1.75/0.58    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 1.75/0.58    inference(backward_demodulation,[],[f62,f106])).
% 1.75/0.58  fof(f62,plain,(
% 1.75/0.58    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 1.75/0.58    inference(cnf_transformation,[],[f52])).
% 1.75/0.58  fof(f137,plain,(
% 1.75/0.58    v5_relat_1(sK2,k2_struct_0(sK1))),
% 1.75/0.58    inference(unit_resulting_resolution,[],[f116,f86])).
% 1.75/0.58  fof(f86,plain,(
% 1.75/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.75/0.58    inference(cnf_transformation,[],[f38])).
% 1.75/0.58  fof(f38,plain,(
% 1.75/0.58    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.58    inference(ennf_transformation,[],[f21])).
% 1.75/0.58  fof(f21,plain,(
% 1.75/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.75/0.58    inference(pure_predicate_removal,[],[f7])).
% 1.75/0.58  fof(f7,axiom,(
% 1.75/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.75/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.75/0.58  fof(f145,plain,(
% 1.75/0.58    v1_relat_1(sK2)),
% 1.75/0.58    inference(unit_resulting_resolution,[],[f73,f116,f66])).
% 1.75/0.58  fof(f66,plain,(
% 1.75/0.58    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 1.75/0.58    inference(cnf_transformation,[],[f26])).
% 1.75/0.58  fof(f26,plain,(
% 1.75/0.58    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.75/0.58    inference(ennf_transformation,[],[f1])).
% 1.75/0.58  fof(f1,axiom,(
% 1.75/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.75/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.75/0.58  fof(f73,plain,(
% 1.75/0.58    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.75/0.58    inference(cnf_transformation,[],[f3])).
% 1.75/0.58  fof(f3,axiom,(
% 1.75/0.58    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.75/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.75/0.58  fof(f258,plain,(
% 1.75/0.58    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 1.75/0.58    inference(unit_resulting_resolution,[],[f145,f59,f233,f77])).
% 1.75/0.58  fof(f77,plain,(
% 1.75/0.58    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.75/0.58    inference(cnf_transformation,[],[f35])).
% 1.75/0.58  fof(f59,plain,(
% 1.75/0.58    v1_funct_1(sK2)),
% 1.75/0.58    inference(cnf_transformation,[],[f52])).
% 1.75/0.58  fof(f506,plain,(
% 1.75/0.58    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | k1_xboole_0 = k2_relat_1(sK2)),
% 1.75/0.58    inference(backward_demodulation,[],[f326,f505])).
% 1.75/0.58  fof(f505,plain,(
% 1.75/0.58    sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 1.75/0.58    inference(forward_demodulation,[],[f498,f180])).
% 1.75/0.58  fof(f180,plain,(
% 1.75/0.58    sK2 = k2_funct_1(k2_funct_1(sK2))),
% 1.75/0.58    inference(unit_resulting_resolution,[],[f63,f59,f145,f70])).
% 1.75/0.58  fof(f70,plain,(
% 1.75/0.58    ( ! [X0] : (~v2_funct_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.75/0.58    inference(cnf_transformation,[],[f30])).
% 1.75/0.58  fof(f30,plain,(
% 1.75/0.58    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.75/0.58    inference(flattening,[],[f29])).
% 1.75/0.58  fof(f29,plain,(
% 1.75/0.58    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.75/0.58    inference(ennf_transformation,[],[f6])).
% 1.75/0.58  fof(f6,axiom,(
% 1.75/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 1.75/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
% 1.75/0.58  fof(f63,plain,(
% 1.75/0.58    v2_funct_1(sK2)),
% 1.75/0.58    inference(cnf_transformation,[],[f52])).
% 1.75/0.58  fof(f498,plain,(
% 1.75/0.58    k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 1.75/0.58    inference(unit_resulting_resolution,[],[f178,f179,f379,f380,f440,f99])).
% 1.75/0.58  fof(f99,plain,(
% 1.75/0.58    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.75/0.58    inference(cnf_transformation,[],[f46])).
% 1.75/0.58  fof(f46,plain,(
% 1.75/0.58    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.75/0.58    inference(flattening,[],[f45])).
% 1.75/0.58  fof(f45,plain,(
% 1.75/0.58    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.75/0.58    inference(ennf_transformation,[],[f16])).
% 1.75/0.58  fof(f16,axiom,(
% 1.75/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 1.75/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 1.75/0.58  fof(f440,plain,(
% 1.75/0.58    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 1.75/0.58    inference(forward_demodulation,[],[f425,f182])).
% 1.75/0.58  fof(f182,plain,(
% 1.75/0.58    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.75/0.58    inference(unit_resulting_resolution,[],[f63,f59,f145,f72])).
% 1.75/0.58  fof(f72,plain,(
% 1.75/0.58    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.75/0.58    inference(cnf_transformation,[],[f32])).
% 1.75/0.58  fof(f32,plain,(
% 1.75/0.58    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.75/0.58    inference(flattening,[],[f31])).
% 1.75/0.58  fof(f31,plain,(
% 1.75/0.58    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.75/0.58    inference(ennf_transformation,[],[f5])).
% 1.75/0.58  fof(f5,axiom,(
% 1.75/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.75/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.75/0.58  fof(f425,plain,(
% 1.75/0.58    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 1.75/0.58    inference(unit_resulting_resolution,[],[f380,f85])).
% 1.75/0.58  fof(f380,plain,(
% 1.75/0.58    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 1.75/0.58    inference(unit_resulting_resolution,[],[f59,f63,f258,f259,f300,f98])).
% 1.75/0.58  fof(f98,plain,(
% 1.75/0.58    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.75/0.58    inference(cnf_transformation,[],[f44])).
% 1.75/0.58  fof(f44,plain,(
% 1.75/0.58    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.75/0.58    inference(flattening,[],[f43])).
% 1.75/0.58  fof(f43,plain,(
% 1.75/0.58    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.75/0.58    inference(ennf_transformation,[],[f13])).
% 1.75/0.58  fof(f13,axiom,(
% 1.75/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.75/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 1.75/0.58  fof(f300,plain,(
% 1.75/0.58    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 1.75/0.58    inference(unit_resulting_resolution,[],[f259,f85])).
% 1.75/0.58  fof(f379,plain,(
% 1.75/0.58    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))),
% 1.75/0.58    inference(unit_resulting_resolution,[],[f59,f63,f258,f259,f300,f97])).
% 1.75/0.58  fof(f97,plain,(
% 1.75/0.58    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_2(k2_funct_1(X2),X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.75/0.58    inference(cnf_transformation,[],[f44])).
% 1.75/0.58  fof(f179,plain,(
% 1.75/0.58    v2_funct_1(k2_funct_1(sK2))),
% 1.75/0.58    inference(unit_resulting_resolution,[],[f63,f59,f145,f69])).
% 1.75/0.58  fof(f69,plain,(
% 1.75/0.58    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.75/0.58    inference(cnf_transformation,[],[f28])).
% 1.75/0.58  fof(f28,plain,(
% 1.75/0.58    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.75/0.58    inference(flattening,[],[f27])).
% 1.75/0.58  fof(f27,plain,(
% 1.75/0.58    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.75/0.58    inference(ennf_transformation,[],[f4])).
% 1.75/0.58  fof(f4,axiom,(
% 1.75/0.58    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.75/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).
% 1.75/0.58  fof(f178,plain,(
% 1.75/0.58    v1_funct_1(k2_funct_1(sK2))),
% 1.75/0.58    inference(unit_resulting_resolution,[],[f63,f59,f145,f68])).
% 1.75/0.58  fof(f68,plain,(
% 1.75/0.58    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.75/0.58    inference(cnf_transformation,[],[f28])).
% 1.75/0.58  fof(f326,plain,(
% 1.75/0.58    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2) | k1_xboole_0 = k2_relat_1(sK2)),
% 1.75/0.58    inference(superposition,[],[f274,f168])).
% 1.75/0.58  fof(f168,plain,(
% 1.75/0.58    k2_struct_0(sK0) = k1_relat_1(sK2) | k1_xboole_0 = k2_relat_1(sK2)),
% 1.75/0.58    inference(forward_demodulation,[],[f167,f163])).
% 1.75/0.58  fof(f163,plain,(
% 1.75/0.58    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 1.75/0.58    inference(forward_demodulation,[],[f135,f151])).
% 1.75/0.58  fof(f135,plain,(
% 1.75/0.58    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.75/0.58    inference(unit_resulting_resolution,[],[f116,f84])).
% 1.75/0.58  fof(f84,plain,(
% 1.75/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.75/0.58    inference(cnf_transformation,[],[f36])).
% 1.75/0.58  fof(f36,plain,(
% 1.75/0.58    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.58    inference(ennf_transformation,[],[f8])).
% 1.75/0.58  fof(f8,axiom,(
% 1.75/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.75/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.75/0.58  fof(f167,plain,(
% 1.75/0.58    k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | k1_xboole_0 = k2_relat_1(sK2)),
% 1.75/0.58    inference(forward_demodulation,[],[f166,f151])).
% 1.75/0.58  fof(f166,plain,(
% 1.75/0.58    k1_xboole_0 = k2_relat_1(sK2) | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.75/0.58    inference(forward_demodulation,[],[f165,f151])).
% 1.75/0.58  fof(f165,plain,(
% 1.75/0.58    k1_xboole_0 = k2_struct_0(sK1) | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.75/0.58    inference(subsumption_resolution,[],[f164,f155])).
% 1.75/0.58  fof(f164,plain,(
% 1.75/0.58    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | k1_xboole_0 = k2_struct_0(sK1) | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.75/0.58    inference(forward_demodulation,[],[f146,f151])).
% 1.75/0.58  fof(f146,plain,(
% 1.75/0.58    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k1_xboole_0 = k2_struct_0(sK1) | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.75/0.58    inference(resolution,[],[f116,f87])).
% 1.75/0.58  fof(f87,plain,(
% 1.75/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.75/0.58    inference(cnf_transformation,[],[f56])).
% 1.75/0.58  fof(f56,plain,(
% 1.75/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.58    inference(nnf_transformation,[],[f40])).
% 1.75/0.58  fof(f40,plain,(
% 1.75/0.58    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.58    inference(flattening,[],[f39])).
% 1.75/0.58  fof(f39,plain,(
% 1.75/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.58    inference(ennf_transformation,[],[f10])).
% 1.75/0.58  fof(f10,axiom,(
% 1.75/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.75/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.75/0.58  fof(f274,plain,(
% 1.75/0.58    ~r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),sK2)),
% 1.75/0.58    inference(backward_demodulation,[],[f153,f270])).
% 1.75/0.58  fof(f270,plain,(
% 1.75/0.58    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 1.75/0.58    inference(unit_resulting_resolution,[],[f59,f63,f155,f154,f156,f99])).
% 1.75/0.58  fof(f156,plain,(
% 1.75/0.58    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 1.75/0.58    inference(backward_demodulation,[],[f136,f151])).
% 1.75/0.58  fof(f154,plain,(
% 1.75/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 1.75/0.58    inference(backward_demodulation,[],[f116,f151])).
% 1.75/0.58  fof(f153,plain,(
% 1.75/0.58    ~r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2)),
% 1.75/0.58    inference(backward_demodulation,[],[f114,f151])).
% 1.75/0.58  fof(f114,plain,(
% 1.75/0.58    ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)),
% 1.75/0.58    inference(backward_demodulation,[],[f111,f112])).
% 1.75/0.58  fof(f111,plain,(
% 1.75/0.58    ~r2_funct_2(k2_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 1.75/0.58    inference(backward_demodulation,[],[f64,f106])).
% 1.75/0.58  fof(f64,plain,(
% 1.75/0.58    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 1.75/0.58    inference(cnf_transformation,[],[f52])).
% 1.75/0.58  fof(f155,plain,(
% 1.75/0.58    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 1.75/0.58    inference(backward_demodulation,[],[f117,f151])).
% 1.75/0.58  fof(f117,plain,(
% 1.75/0.58    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 1.75/0.58    inference(backward_demodulation,[],[f108,f112])).
% 1.75/0.58  fof(f108,plain,(
% 1.75/0.58    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))),
% 1.75/0.58    inference(backward_demodulation,[],[f60,f106])).
% 1.75/0.58  fof(f60,plain,(
% 1.75/0.58    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.75/0.58    inference(cnf_transformation,[],[f52])).
% 1.75/0.58  fof(f647,plain,(
% 1.75/0.58    ~v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) | k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 = sK2),
% 1.75/0.58    inference(resolution,[],[f521,f103])).
% 1.75/0.58  fof(f103,plain,(
% 1.75/0.58    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2) )),
% 1.75/0.58    inference(equality_resolution,[],[f91])).
% 1.75/0.58  fof(f91,plain,(
% 1.75/0.58    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.75/0.58    inference(cnf_transformation,[],[f56])).
% 1.75/0.58  fof(f521,plain,(
% 1.75/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))),
% 1.75/0.58    inference(backward_demodulation,[],[f154,f516])).
% 1.75/0.58  fof(f526,plain,(
% 1.75/0.58    r2_funct_2(k2_struct_0(sK0),k1_xboole_0,sK2,sK2)),
% 1.75/0.58    inference(backward_demodulation,[],[f162,f516])).
% 1.75/0.58  fof(f162,plain,(
% 1.75/0.58    r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2)),
% 1.75/0.58    inference(backward_demodulation,[],[f144,f151])).
% 1.75/0.58  fof(f144,plain,(
% 1.75/0.58    r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)),
% 1.75/0.58    inference(unit_resulting_resolution,[],[f59,f59,f117,f117,f116,f116,f100])).
% 1.75/0.58  fof(f1037,plain,(
% 1.75/0.58    ~r2_funct_2(k1_xboole_0,k1_xboole_0,sK2,sK2) | k1_xboole_0 = sK2),
% 1.75/0.58    inference(duplicate_literal_removal,[],[f1034])).
% 1.75/0.58  fof(f1034,plain,(
% 1.75/0.58    ~r2_funct_2(k1_xboole_0,k1_xboole_0,sK2,sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 1.75/0.58    inference(superposition,[],[f683,f862])).
% 1.75/0.58  fof(f862,plain,(
% 1.75/0.58    sK2 = k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) | k1_xboole_0 = sK2),
% 1.75/0.58    inference(superposition,[],[f581,f598])).
% 1.75/0.58  fof(f598,plain,(
% 1.75/0.58    k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 = sK2),
% 1.75/0.58    inference(subsumption_resolution,[],[f575,f533])).
% 1.75/0.58  fof(f533,plain,(
% 1.75/0.58    r1_tarski(k1_xboole_0,k1_xboole_0)),
% 1.75/0.58    inference(backward_demodulation,[],[f233,f516])).
% 1.75/0.58  fof(f575,plain,(
% 1.75/0.58    ~r1_tarski(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 = sK2),
% 1.75/0.58    inference(backward_demodulation,[],[f487,f516])).
% 1.75/0.58  fof(f487,plain,(
% 1.75/0.58    ~r1_tarski(k2_relat_1(sK2),k1_xboole_0) | k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 = sK2),
% 1.75/0.58    inference(subsumption_resolution,[],[f480,f330])).
% 1.75/0.58  fof(f330,plain,(
% 1.75/0.58    ( ! [X0] : (v1_funct_2(sK2,k1_relat_1(sK2),X0) | ~r1_tarski(k2_relat_1(sK2),X0)) )),
% 1.75/0.58    inference(resolution,[],[f121,f145])).
% 1.75/0.58  fof(f121,plain,(
% 1.75/0.58    ( ! [X7] : (~v1_relat_1(sK2) | v1_funct_2(sK2,k1_relat_1(sK2),X7) | ~r1_tarski(k2_relat_1(sK2),X7)) )),
% 1.75/0.58    inference(resolution,[],[f59,f77])).
% 1.75/0.58  fof(f480,plain,(
% 1.75/0.58    ~r1_tarski(k2_relat_1(sK2),k1_xboole_0) | ~v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) | k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 = sK2),
% 1.75/0.58    inference(resolution,[],[f357,f103])).
% 1.75/0.58  fof(f357,plain,(
% 1.75/0.58    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) | ~r1_tarski(k2_relat_1(sK2),X0)) )),
% 1.75/0.58    inference(resolution,[],[f122,f145])).
% 1.75/0.58  fof(f122,plain,(
% 1.75/0.58    ( ! [X8] : (~v1_relat_1(sK2) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X8))) | ~r1_tarski(k2_relat_1(sK2),X8)) )),
% 1.75/0.58    inference(resolution,[],[f59,f78])).
% 1.75/0.58  fof(f581,plain,(
% 1.75/0.58    sK2 = k2_tops_2(k1_xboole_0,k1_relat_1(sK2),k2_funct_1(sK2))),
% 1.75/0.58    inference(backward_demodulation,[],[f505,f516])).
% 1.75/0.58  fof(f683,plain,(
% 1.75/0.58    ~r2_funct_2(k1_xboole_0,k1_xboole_0,k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)),sK2) | k1_xboole_0 = sK2),
% 1.75/0.58    inference(superposition,[],[f539,f663])).
% 1.75/0.58  fof(f539,plain,(
% 1.75/0.58    ~r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),sK2)),
% 1.75/0.58    inference(backward_demodulation,[],[f274,f516])).
% 1.75/0.58  fof(f978,plain,(
% 1.75/0.58    k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2))),
% 1.75/0.58    inference(subsumption_resolution,[],[f971,f546])).
% 1.75/0.58  fof(f546,plain,(
% 1.75/0.58    v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0)),
% 1.75/0.58    inference(backward_demodulation,[],[f335,f516])).
% 1.75/0.58  fof(f335,plain,(
% 1.75/0.58    v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2))),
% 1.75/0.58    inference(unit_resulting_resolution,[],[f178,f272,f273,f94])).
% 1.75/0.58  fof(f94,plain,(
% 1.75/0.58    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)) )),
% 1.75/0.58    inference(cnf_transformation,[],[f42])).
% 1.75/0.58  fof(f42,plain,(
% 1.75/0.58    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.75/0.58    inference(flattening,[],[f41])).
% 1.75/0.58  fof(f41,plain,(
% 1.75/0.58    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.75/0.58    inference(ennf_transformation,[],[f17])).
% 1.75/0.58  fof(f17,axiom,(
% 1.75/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 1.75/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).
% 1.75/0.58  fof(f273,plain,(
% 1.75/0.58    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))),
% 1.75/0.58    inference(unit_resulting_resolution,[],[f59,f63,f155,f154,f156,f98])).
% 1.75/0.58  fof(f272,plain,(
% 1.75/0.58    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))),
% 1.75/0.58    inference(unit_resulting_resolution,[],[f59,f63,f155,f154,f156,f97])).
% 1.75/0.58  fof(f971,plain,(
% 1.75/0.58    ~v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) | k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2))),
% 1.75/0.58    inference(resolution,[],[f547,f103])).
% 1.75/0.58  fof(f547,plain,(
% 1.75/0.58    m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))),
% 1.75/0.58    inference(backward_demodulation,[],[f336,f516])).
% 1.75/0.58  fof(f336,plain,(
% 1.75/0.58    m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 1.75/0.58    inference(unit_resulting_resolution,[],[f178,f272,f273,f95])).
% 1.75/0.58  fof(f95,plain,(
% 1.75/0.58    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.75/0.58    inference(cnf_transformation,[],[f42])).
% 1.75/0.58  fof(f1087,plain,(
% 1.75/0.58    ~r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k1_xboole_0)),
% 1.75/0.58    inference(backward_demodulation,[],[f539,f1041])).
% 1.75/0.58  fof(f1075,plain,(
% 1.75/0.58    r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.75/0.58    inference(backward_demodulation,[],[f526,f1041])).
% 1.75/0.58  fof(f1788,plain,(
% 1.75/0.58    ~r2_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.75/0.58    inference(backward_demodulation,[],[f1642,f1758])).
% 1.75/0.58  fof(f1758,plain,(
% 1.75/0.58    k1_xboole_0 = k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0))),
% 1.75/0.58    inference(backward_demodulation,[],[f1116,f1738])).
% 1.75/0.58  fof(f1738,plain,(
% 1.75/0.58    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.75/0.58    inference(backward_demodulation,[],[f1638,f1706])).
% 1.75/0.58  fof(f1706,plain,(
% 1.75/0.58    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.75/0.58    inference(unit_resulting_resolution,[],[f1635,f1634,f105])).
% 1.75/0.58  fof(f105,plain,(
% 1.75/0.58    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)) )),
% 1.75/0.58    inference(equality_resolution,[],[f88])).
% 1.75/0.58  fof(f88,plain,(
% 1.75/0.58    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.75/0.58    inference(cnf_transformation,[],[f56])).
% 1.75/0.58  fof(f1634,plain,(
% 1.75/0.58    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.75/0.58    inference(backward_demodulation,[],[f1071,f1625])).
% 1.75/0.58  fof(f1071,plain,(
% 1.75/0.58    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))),
% 1.75/0.58    inference(backward_demodulation,[],[f521,f1041])).
% 1.75/0.58  fof(f1635,plain,(
% 1.75/0.58    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.75/0.58    inference(backward_demodulation,[],[f1072,f1625])).
% 1.75/0.58  fof(f1072,plain,(
% 1.75/0.58    v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0)),
% 1.75/0.58    inference(backward_demodulation,[],[f522,f1041])).
% 1.75/0.58  fof(f1638,plain,(
% 1.75/0.58    k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.75/0.58    inference(backward_demodulation,[],[f1076,f1625])).
% 1.75/0.58  fof(f1076,plain,(
% 1.75/0.58    k1_relat_1(k1_xboole_0) = k1_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0)),
% 1.75/0.58    inference(backward_demodulation,[],[f527,f1041])).
% 1.75/0.58  fof(f527,plain,(
% 1.75/0.58    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2)),
% 1.75/0.58    inference(backward_demodulation,[],[f163,f516])).
% 1.75/0.58  fof(f1116,plain,(
% 1.75/0.58    k1_xboole_0 = k2_tops_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k2_funct_1(k1_xboole_0))),
% 1.75/0.58    inference(backward_demodulation,[],[f581,f1041])).
% 1.75/0.58  fof(f1642,plain,(
% 1.75/0.58    ~r2_funct_2(k1_xboole_0,k1_xboole_0,k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)),k1_xboole_0)),
% 1.75/0.58    inference(backward_demodulation,[],[f1087,f1625])).
% 1.75/0.58  % SZS output end Proof for theBenchmark
% 1.75/0.58  % (26838)------------------------------
% 1.75/0.58  % (26838)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.58  % (26838)Termination reason: Refutation
% 1.75/0.58  
% 1.75/0.58  % (26838)Memory used [KB]: 6908
% 1.75/0.58  % (26838)Time elapsed: 0.163 s
% 1.75/0.58  % (26838)------------------------------
% 1.75/0.58  % (26838)------------------------------
% 1.75/0.58  % (26822)Success in time 0.222 s
%------------------------------------------------------------------------------
