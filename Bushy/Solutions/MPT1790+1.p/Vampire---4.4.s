%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t105_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:03 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 324 expanded)
%              Number of leaves         :   11 ( 121 expanded)
%              Depth                    :   15
%              Number of atoms          :  272 (2051 expanded)
%              Number of equality atoms :   41 ( 339 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f502,plain,(
    $false ),
    inference(subsumption_resolution,[],[f496,f174])).

fof(f174,plain,(
    r2_hidden(sK1,k5_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f173,f82])).

fof(f82,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,
    ( ~ v3_pre_topc(sK2,k6_tmap_1(sK0,sK1))
    & sK1 = sK2
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f50,f72,f71,f70])).

fof(f70,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v3_pre_topc(X2,k6_tmap_1(X0,X1))
                & X1 = X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_pre_topc(X2,k6_tmap_1(sK0,X1))
              & X1 = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X1)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_pre_topc(X2,k6_tmap_1(X0,X1))
              & X1 = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ v3_pre_topc(X2,k6_tmap_1(X0,sK1))
            & sK1 = X2
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,sK1)))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,k6_tmap_1(X0,X1))
          & X1 = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
     => ( ~ v3_pre_topc(sK2,k6_tmap_1(X0,X1))
        & sK2 = X1
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_pre_topc(X2,k6_tmap_1(X0,X1))
              & X1 = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_pre_topc(X2,k6_tmap_1(X0,X1))
              & X1 = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))
               => ( X1 = X2
                 => v3_pre_topc(X2,k6_tmap_1(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))
             => ( X1 = X2
               => v3_pre_topc(X2,k6_tmap_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t105_tmap_1.p',t105_tmap_1)).

fof(f173,plain,
    ( r2_hidden(sK1,k5_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f172,f83])).

fof(f83,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f73])).

fof(f172,plain,
    ( r2_hidden(sK1,k5_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f153,f84])).

fof(f84,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f73])).

fof(f153,plain,
    ( r2_hidden(sK1,k5_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f85,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k5_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r2_hidden(X1,k5_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t105_tmap_1.p',t102_tmap_1)).

fof(f85,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f73])).

fof(f496,plain,(
    ~ r2_hidden(sK1,k5_tmap_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f477,f201])).

fof(f201,plain,(
    ~ r2_hidden(sK1,u1_pre_topc(k6_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f200,f165])).

fof(f165,plain,(
    l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f164,f82])).

fof(f164,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f163,f83])).

fof(f163,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f150,f84])).

fof(f150,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f85,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t105_tmap_1.p',dt_k6_tmap_1)).

fof(f200,plain,
    ( ~ r2_hidden(sK1,u1_pre_topc(k6_tmap_1(sK0,sK1)))
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f199,f111])).

fof(f111,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f86,f87])).

fof(f87,plain,(
    sK1 = sK2 ),
    inference(cnf_transformation,[],[f73])).

fof(f86,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) ),
    inference(cnf_transformation,[],[f73])).

fof(f199,plain,
    ( ~ r2_hidden(sK1,u1_pre_topc(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f110,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t105_tmap_1.p',d5_pre_topc)).

fof(f110,plain,(
    ~ v3_pre_topc(sK1,k6_tmap_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f87,f88])).

fof(f88,plain,(
    ~ v3_pre_topc(sK2,k6_tmap_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f73])).

fof(f477,plain,(
    u1_pre_topc(k6_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f476])).

fof(f476,plain,
    ( k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,sK1)
    | u1_pre_topc(k6_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,sK1) ),
    inference(superposition,[],[f259,f176])).

fof(f176,plain,(
    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_pre_topc(k6_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f175,f165])).

fof(f175,plain,
    ( k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_pre_topc(k6_tmap_1(sK0,sK1)))
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f159,f105])).

fof(f105,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t105_tmap_1.p',abstractness_v1_pre_topc)).

fof(f159,plain,(
    v1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f158,f82])).

fof(f158,plain,
    ( v1_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f157,f83])).

fof(f157,plain,
    ( v1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f148,f84])).

fof(f148,plain,
    ( v1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f85,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f259,plain,(
    ! [X2,X3] :
      ( k6_tmap_1(sK0,sK1) != g1_pre_topc(X3,X2)
      | k5_tmap_1(sK0,sK1) = X2 ) ),
    inference(forward_demodulation,[],[f254,f168])).

fof(f168,plain,(
    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f167,f82])).

fof(f167,plain,
    ( k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f166,f83])).

fof(f166,plain,
    ( k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f151,f84])).

fof(f151,plain,
    ( k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f85,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t105_tmap_1.p',d9_tmap_1)).

fof(f254,plain,(
    ! [X2,X3] :
      ( k5_tmap_1(sK0,sK1) = X2
      | g1_pre_topc(X3,X2) != g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) ) ),
    inference(resolution,[],[f171,f107])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t105_tmap_1.p',free_g1_pre_topc)).

fof(f171,plain,(
    m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f170,f82])).

fof(f170,plain,
    ( m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f169,f83])).

fof(f169,plain,
    ( m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f152,f84])).

fof(f152,plain,
    ( m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f85,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t105_tmap_1.p',dt_k5_tmap_1)).
%------------------------------------------------------------------------------
