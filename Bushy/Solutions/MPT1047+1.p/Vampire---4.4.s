%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t164_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:35 EDT 2019

% Result     : Theorem 31.05s
% Output     : Refutation 31.05s
% Verified   : 
% Statistics : Number of formulae       :  135 (1397 expanded)
%              Number of leaves         :   13 ( 254 expanded)
%              Depth                    :   45
%              Number of atoms          :  551 (6898 expanded)
%              Number of equality atoms :  101 (1338 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16791,plain,(
    $false ),
    inference(subsumption_resolution,[],[f16790,f112])).

fof(f112,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t164_funct_2.p',d1_tarski)).

fof(f16790,plain,(
    ~ r2_hidden(sK3,k1_tarski(sK3)) ),
    inference(forward_demodulation,[],[f16789,f16704])).

fof(f16704,plain,(
    sK3 = sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)) ),
    inference(subsumption_resolution,[],[f16703,f68])).

fof(f68,plain,(
    k1_tarski(sK3) != k5_partfun1(sK0,k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
              & v1_funct_2(X3,X0,k1_tarski(X1))
              & v1_funct_1(X3) )
           => k1_tarski(X3) = k5_partfun1(X0,k1_tarski(X1),X2) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => k1_tarski(X3) = k5_partfun1(X0,k1_tarski(X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t164_funct_2.p',t164_funct_2)).

fof(f16703,plain,
    ( sK3 = sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3))
    | k1_tarski(sK3) = k5_partfun1(sK0,k1_tarski(sK1),sK2) ),
    inference(equality_resolution,[],[f16601])).

fof(f16601,plain,(
    ! [X0] :
      ( sK3 != X0
      | sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(X0)) = X0
      | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) ) ),
    inference(equality_factoring,[],[f15806])).

fof(f15806,plain,(
    ! [X1] :
      ( sK3 = sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(X1))
      | sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(X1)) = X1
      | k1_tarski(X1) = k5_partfun1(sK0,k1_tarski(sK1),sK2) ) ),
    inference(duplicate_literal_removal,[],[f15697])).

fof(f15697,plain,(
    ! [X1] :
      ( sK3 = sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(X1))
      | k1_tarski(X1) = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(X1)) = X1
      | k1_tarski(X1) = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(X1)) = X1 ) ),
    inference(superposition,[],[f13551,f357])).

fof(f357,plain,(
    ! [X6] :
      ( sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(X6)) = sK7(sK0,k1_tarski(sK1),sK2,k1_tarski(X6))
      | k1_tarski(X6) = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(X6)) = X6 ) ),
    inference(resolution,[],[f170,f110])).

fof(f110,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f170,plain,(
    ! [X3] :
      ( r2_hidden(sK5(sK0,k1_tarski(sK1),sK2,X3),X3)
      | sK5(sK0,k1_tarski(sK1),sK2,X3) = sK7(sK0,k1_tarski(sK1),sK2,X3)
      | k5_partfun1(sK0,k1_tarski(sK1),sK2) = X3 ) ),
    inference(subsumption_resolution,[],[f159,f69])).

fof(f69,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f159,plain,(
    ! [X3] :
      ( ~ v1_funct_1(sK2)
      | sK5(sK0,k1_tarski(sK1),sK2,X3) = sK7(sK0,k1_tarski(sK1),sK2,X3)
      | r2_hidden(sK5(sK0,k1_tarski(sK1),sK2,X3),X3)
      | k5_partfun1(sK0,k1_tarski(sK1),sK2) = X3 ) ),
    inference(resolution,[],[f70,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | sK5(X0,X1,X2,X3) = sK7(X0,X1,X2,X3)
      | r2_hidden(sK5(X0,X1,X2,X3),X3)
      | k5_partfun1(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t164_funct_2.p',d7_partfun1)).

fof(f70,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f34])).

fof(f13551,plain,(
    ! [X6] :
      ( sK3 = sK7(sK0,k1_tarski(sK1),sK2,k1_tarski(X6))
      | k1_tarski(X6) = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(X6)) = X6 ) ),
    inference(subsumption_resolution,[],[f13542,f101])).

fof(f101,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t164_funct_2.p',fc2_xboole_0)).

fof(f13542,plain,(
    ! [X6] :
      ( sK3 = sK7(sK0,k1_tarski(sK1),sK2,k1_tarski(X6))
      | v1_xboole_0(k1_tarski(X6))
      | k1_tarski(X6) = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(X6)) = X6 ) ),
    inference(resolution,[],[f13298,f110])).

fof(f13298,plain,(
    ! [X143] :
      ( r2_hidden(sK5(sK0,k1_tarski(sK1),sK2,X143),X143)
      | sK3 = sK7(sK0,k1_tarski(sK1),sK2,X143)
      | v1_xboole_0(X143)
      | k5_partfun1(sK0,k1_tarski(sK1),sK2) = X143 ) ),
    inference(resolution,[],[f13098,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t164_funct_2.p',t2_subset)).

fof(f13098,plain,(
    ! [X1] :
      ( m1_subset_1(sK5(sK0,k1_tarski(sK1),sK2,X1),X1)
      | k5_partfun1(sK0,k1_tarski(sK1),sK2) = X1
      | sK3 = sK7(sK0,k1_tarski(sK1),sK2,X1) ) ),
    inference(subsumption_resolution,[],[f13097,f326])).

fof(f326,plain,(
    ! [X2] :
      ( m1_subset_1(sK7(sK0,k1_tarski(sK1),sK2,X2),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      | m1_subset_1(sK5(sK0,k1_tarski(sK1),sK2,X2),X2)
      | k5_partfun1(sK0,k1_tarski(sK1),sK2) = X2 ) ),
    inference(resolution,[],[f169,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t164_funct_2.p',t1_subset)).

fof(f169,plain,(
    ! [X2] :
      ( r2_hidden(sK5(sK0,k1_tarski(sK1),sK2,X2),X2)
      | m1_subset_1(sK7(sK0,k1_tarski(sK1),sK2,X2),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      | k5_partfun1(sK0,k1_tarski(sK1),sK2) = X2 ) ),
    inference(subsumption_resolution,[],[f158,f69])).

fof(f158,plain,(
    ! [X2] :
      ( ~ v1_funct_1(sK2)
      | m1_subset_1(sK7(sK0,k1_tarski(sK1),sK2,X2),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      | r2_hidden(sK5(sK0,k1_tarski(sK1),sK2,X2),X2)
      | k5_partfun1(sK0,k1_tarski(sK1),sK2) = X2 ) ),
    inference(resolution,[],[f70,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | m1_subset_1(sK7(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK5(X0,X1,X2,X3),X3)
      | k5_partfun1(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f13097,plain,(
    ! [X1] :
      ( k5_partfun1(sK0,k1_tarski(sK1),sK2) = X1
      | m1_subset_1(sK5(sK0,k1_tarski(sK1),sK2,X1),X1)
      | ~ m1_subset_1(sK7(sK0,k1_tarski(sK1),sK2,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      | sK3 = sK7(sK0,k1_tarski(sK1),sK2,X1) ) ),
    inference(subsumption_resolution,[],[f13092,f67])).

fof(f67,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f34])).

fof(f13092,plain,(
    ! [X1] :
      ( k5_partfun1(sK0,k1_tarski(sK1),sK2) = X1
      | m1_subset_1(sK5(sK0,k1_tarski(sK1),sK2,X1),X1)
      | ~ m1_subset_1(sK7(sK0,k1_tarski(sK1),sK2,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      | sK3 = sK7(sK0,k1_tarski(sK1),sK2,X1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ) ),
    inference(resolution,[],[f11924,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t164_funct_2.p',redefinition_r2_relset_1)).

fof(f11924,plain,(
    ! [X0] :
      ( r2_relset_1(sK0,k1_tarski(sK1),sK3,sK7(sK0,k1_tarski(sK1),sK2,X0))
      | k5_partfun1(sK0,k1_tarski(sK1),sK2) = X0
      | m1_subset_1(sK5(sK0,k1_tarski(sK1),sK2,X0),X0) ) ),
    inference(subsumption_resolution,[],[f11923,f326])).

fof(f11923,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(sK0,k1_tarski(sK1),sK2,X0),X0)
      | k5_partfun1(sK0,k1_tarski(sK1),sK2) = X0
      | ~ m1_subset_1(sK7(sK0,k1_tarski(sK1),sK2,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      | r2_relset_1(sK0,k1_tarski(sK1),sK3,sK7(sK0,k1_tarski(sK1),sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f11918,f255])).

fof(f255,plain,(
    ! [X2] :
      ( m1_subset_1(sK5(sK0,k1_tarski(sK1),sK2,X2),X2)
      | k5_partfun1(sK0,k1_tarski(sK1),sK2) = X2
      | v1_funct_1(sK7(sK0,k1_tarski(sK1),sK2,X2)) ) ),
    inference(resolution,[],[f168,f98])).

fof(f168,plain,(
    ! [X1] :
      ( r2_hidden(sK5(sK0,k1_tarski(sK1),sK2,X1),X1)
      | v1_funct_1(sK7(sK0,k1_tarski(sK1),sK2,X1))
      | k5_partfun1(sK0,k1_tarski(sK1),sK2) = X1 ) ),
    inference(subsumption_resolution,[],[f157,f69])).

fof(f157,plain,(
    ! [X1] :
      ( ~ v1_funct_1(sK2)
      | v1_funct_1(sK7(sK0,k1_tarski(sK1),sK2,X1))
      | r2_hidden(sK5(sK0,k1_tarski(sK1),sK2,X1),X1)
      | k5_partfun1(sK0,k1_tarski(sK1),sK2) = X1 ) ),
    inference(resolution,[],[f70,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | v1_funct_1(sK7(X0,X1,X2,X3))
      | r2_hidden(sK5(X0,X1,X2,X3),X3)
      | k5_partfun1(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f11918,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(sK0,k1_tarski(sK1),sK2,X0),X0)
      | k5_partfun1(sK0,k1_tarski(sK1),sK2) = X0
      | ~ v1_funct_1(sK7(sK0,k1_tarski(sK1),sK2,X0))
      | ~ m1_subset_1(sK7(sK0,k1_tarski(sK1),sK2,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      | r2_relset_1(sK0,k1_tarski(sK1),sK3,sK7(sK0,k1_tarski(sK1),sK2,X0)) ) ),
    inference(resolution,[],[f11759,f131])).

fof(f131,plain,(
    ! [X0] :
      ( ~ v1_funct_2(X0,sK0,k1_tarski(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      | r2_relset_1(sK0,k1_tarski(sK1),sK3,X0) ) ),
    inference(subsumption_resolution,[],[f130,f67])).

fof(f130,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,sK0,k1_tarski(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      | r2_relset_1(sK0,k1_tarski(sK1),sK3,X0) ) ),
    inference(subsumption_resolution,[],[f128,f65])).

fof(f65,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f128,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,sK0,k1_tarski(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      | r2_relset_1(sK0,k1_tarski(sK1),sK3,X0) ) ),
    inference(resolution,[],[f66,f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,X0,k1_tarski(X1))
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,k1_tarski(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | r2_relset_1(X0,k1_tarski(X1),X2,X3) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,k1_tarski(X1),X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_2(X3,X0,k1_tarski(X1))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X2,X0,k1_tarski(X1))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,k1_tarski(X1),X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_2(X3,X0,k1_tarski(X1))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X2,X0,k1_tarski(X1))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X2,X0,k1_tarski(X1))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => r2_relset_1(X0,k1_tarski(X1),X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t164_funct_2.p',t66_funct_2)).

fof(f66,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f11759,plain,(
    ! [X1] :
      ( v1_funct_2(sK7(sK0,k1_tarski(sK1),sK2,X1),sK0,k1_tarski(sK1))
      | m1_subset_1(sK5(sK0,k1_tarski(sK1),sK2,X1),X1)
      | k5_partfun1(sK0,k1_tarski(sK1),sK2) = X1 ) ),
    inference(subsumption_resolution,[],[f11758,f69])).

fof(f11758,plain,(
    ! [X1] :
      ( k5_partfun1(sK0,k1_tarski(sK1),sK2) = X1
      | m1_subset_1(sK5(sK0,k1_tarski(sK1),sK2,X1),X1)
      | ~ v1_funct_1(sK2)
      | v1_funct_2(sK7(sK0,k1_tarski(sK1),sK2,X1),sK0,k1_tarski(sK1)) ) ),
    inference(subsumption_resolution,[],[f11744,f70])).

fof(f11744,plain,(
    ! [X1] :
      ( k5_partfun1(sK0,k1_tarski(sK1),sK2) = X1
      | m1_subset_1(sK5(sK0,k1_tarski(sK1),sK2,X1),X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      | ~ v1_funct_1(sK2)
      | v1_funct_2(sK7(sK0,k1_tarski(sK1),sK2,X1),sK0,k1_tarski(sK1)) ) ),
    inference(resolution,[],[f5309,f91])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | v1_funct_2(X3,X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t164_funct_2.p',t158_funct_2)).

fof(f5309,plain,(
    ! [X0] :
      ( r2_hidden(sK7(sK0,k1_tarski(sK1),sK2,X0),k5_partfun1(sK0,k1_tarski(sK1),sK2))
      | k5_partfun1(sK0,k1_tarski(sK1),sK2) = X0
      | m1_subset_1(sK5(sK0,k1_tarski(sK1),sK2,X0),X0) ) ),
    inference(subsumption_resolution,[],[f5308,f98])).

fof(f5308,plain,(
    ! [X0] :
      ( k5_partfun1(sK0,k1_tarski(sK1),sK2) = X0
      | r2_hidden(sK5(sK0,k1_tarski(sK1),sK2,X0),X0)
      | r2_hidden(sK7(sK0,k1_tarski(sK1),sK2,X0),k5_partfun1(sK0,k1_tarski(sK1),sK2))
      | m1_subset_1(sK5(sK0,k1_tarski(sK1),sK2,X0),X0) ) ),
    inference(subsumption_resolution,[],[f5307,f70])).

fof(f5307,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      | k5_partfun1(sK0,k1_tarski(sK1),sK2) = X0
      | r2_hidden(sK5(sK0,k1_tarski(sK1),sK2,X0),X0)
      | r2_hidden(sK7(sK0,k1_tarski(sK1),sK2,X0),k5_partfun1(sK0,k1_tarski(sK1),sK2))
      | m1_subset_1(sK5(sK0,k1_tarski(sK1),sK2,X0),X0) ) ),
    inference(duplicate_literal_removal,[],[f5288])).

fof(f5288,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      | k5_partfun1(sK0,k1_tarski(sK1),sK2) = X0
      | r2_hidden(sK5(sK0,k1_tarski(sK1),sK2,X0),X0)
      | r2_hidden(sK7(sK0,k1_tarski(sK1),sK2,X0),k5_partfun1(sK0,k1_tarski(sK1),sK2))
      | m1_subset_1(sK5(sK0,k1_tarski(sK1),sK2,X0),X0)
      | k5_partfun1(sK0,k1_tarski(sK1),sK2) = X0 ) ),
    inference(resolution,[],[f1508,f326])).

fof(f1508,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK7(sK0,k1_tarski(sK1),sK2,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
      | k5_partfun1(sK0,k1_tarski(sK1),sK2) = X0
      | r2_hidden(sK5(sK0,k1_tarski(sK1),sK2,X0),X0)
      | r2_hidden(sK7(sK0,k1_tarski(sK1),sK2,X0),k5_partfun1(sK0,X1,sK2)) ) ),
    inference(duplicate_literal_removal,[],[f1505])).

fof(f1505,plain,(
    ! [X0,X1] :
      ( k5_partfun1(sK0,k1_tarski(sK1),sK2) = X0
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
      | ~ m1_subset_1(sK7(sK0,k1_tarski(sK1),sK2,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
      | r2_hidden(sK5(sK0,k1_tarski(sK1),sK2,X0),X0)
      | r2_hidden(sK7(sK0,k1_tarski(sK1),sK2,X0),k5_partfun1(sK0,X1,sK2))
      | r2_hidden(sK5(sK0,k1_tarski(sK1),sK2,X0),X0)
      | k5_partfun1(sK0,k1_tarski(sK1),sK2) = X0 ) ),
    inference(resolution,[],[f282,f171])).

fof(f171,plain,(
    ! [X4] :
      ( v1_partfun1(sK7(sK0,k1_tarski(sK1),sK2,X4),sK0)
      | r2_hidden(sK5(sK0,k1_tarski(sK1),sK2,X4),X4)
      | k5_partfun1(sK0,k1_tarski(sK1),sK2) = X4 ) ),
    inference(subsumption_resolution,[],[f160,f69])).

fof(f160,plain,(
    ! [X4] :
      ( ~ v1_funct_1(sK2)
      | v1_partfun1(sK7(sK0,k1_tarski(sK1),sK2,X4),sK0)
      | r2_hidden(sK5(sK0,k1_tarski(sK1),sK2,X4),X4)
      | k5_partfun1(sK0,k1_tarski(sK1),sK2) = X4 ) ),
    inference(resolution,[],[f70,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | v1_partfun1(sK7(X0,X1,X2,X3),X0)
      | r2_hidden(sK5(X0,X1,X2,X3),X3)
      | k5_partfun1(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f282,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_partfun1(sK7(sK0,k1_tarski(sK1),sK2,X1),X2)
      | k5_partfun1(sK0,k1_tarski(sK1),sK2) = X1
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(sK7(sK0,k1_tarski(sK1),sK2,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | r2_hidden(sK5(sK0,k1_tarski(sK1),sK2,X1),X1)
      | r2_hidden(sK7(sK0,k1_tarski(sK1),sK2,X1),k5_partfun1(X2,X3,sK2)) ) ),
    inference(subsumption_resolution,[],[f281,f168])).

fof(f281,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(sK5(sK0,k1_tarski(sK1),sK2,X1),X1)
      | k5_partfun1(sK0,k1_tarski(sK1),sK2) = X1
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(sK7(sK0,k1_tarski(sK1),sK2,X1))
      | ~ m1_subset_1(sK7(sK0,k1_tarski(sK1),sK2,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_partfun1(sK7(sK0,k1_tarski(sK1),sK2,X1),X2)
      | r2_hidden(sK7(sK0,k1_tarski(sK1),sK2,X1),k5_partfun1(X2,X3,sK2)) ) ),
    inference(subsumption_resolution,[],[f277,f69])).

fof(f277,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(sK5(sK0,k1_tarski(sK1),sK2,X1),X1)
      | k5_partfun1(sK0,k1_tarski(sK1),sK2) = X1
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(sK7(sK0,k1_tarski(sK1),sK2,X1))
      | ~ m1_subset_1(sK7(sK0,k1_tarski(sK1),sK2,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_partfun1(sK7(sK0,k1_tarski(sK1),sK2,X1),X2)
      | ~ v1_funct_1(sK2)
      | r2_hidden(sK7(sK0,k1_tarski(sK1),sK2,X1),k5_partfun1(X2,X3,sK2)) ) ),
    inference(resolution,[],[f172,f114])).

fof(f114,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r1_partfun1(X2,X5)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X5,X0)
      | ~ v1_funct_1(X2)
      | r2_hidden(X5,k5_partfun1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f113])).

fof(f113,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X5,X0)
      | ~ r1_partfun1(X2,X5)
      | r2_hidden(X5,X3)
      | k5_partfun1(X0,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X4 != X5
      | ~ v1_partfun1(X5,X0)
      | ~ r1_partfun1(X2,X5)
      | r2_hidden(X4,X3)
      | k5_partfun1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f172,plain,(
    ! [X5] :
      ( r1_partfun1(sK2,sK7(sK0,k1_tarski(sK1),sK2,X5))
      | r2_hidden(sK5(sK0,k1_tarski(sK1),sK2,X5),X5)
      | k5_partfun1(sK0,k1_tarski(sK1),sK2) = X5 ) ),
    inference(subsumption_resolution,[],[f161,f69])).

fof(f161,plain,(
    ! [X5] :
      ( ~ v1_funct_1(sK2)
      | r1_partfun1(sK2,sK7(sK0,k1_tarski(sK1),sK2,X5))
      | r2_hidden(sK5(sK0,k1_tarski(sK1),sK2,X5),X5)
      | k5_partfun1(sK0,k1_tarski(sK1),sK2) = X5 ) ),
    inference(resolution,[],[f70,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | r1_partfun1(X2,sK7(X0,X1,X2,X3))
      | r2_hidden(sK5(X0,X1,X2,X3),X3)
      | k5_partfun1(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f16789,plain,(
    ~ r2_hidden(sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),k1_tarski(sK3)) ),
    inference(subsumption_resolution,[],[f16788,f134])).

fof(f134,plain,(
    v1_partfun1(sK3,sK0) ),
    inference(subsumption_resolution,[],[f133,f101])).

fof(f133,plain,
    ( v1_xboole_0(k1_tarski(sK1))
    | v1_partfun1(sK3,sK0) ),
    inference(subsumption_resolution,[],[f132,f65])).

fof(f132,plain,
    ( ~ v1_funct_1(sK3)
    | v1_xboole_0(k1_tarski(sK1))
    | v1_partfun1(sK3,sK0) ),
    inference(subsumption_resolution,[],[f129,f67])).

fof(f129,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(k1_tarski(sK1))
    | v1_partfun1(sK3,sK0) ),
    inference(resolution,[],[f66,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t164_funct_2.p',cc5_funct_2)).

fof(f16788,plain,
    ( ~ v1_partfun1(sK3,sK0)
    | ~ r2_hidden(sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),k1_tarski(sK3)) ),
    inference(forward_demodulation,[],[f16787,f16704])).

fof(f16787,plain,
    ( ~ v1_partfun1(sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),sK0)
    | ~ r2_hidden(sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),k1_tarski(sK3)) ),
    inference(subsumption_resolution,[],[f16786,f67])).

fof(f16786,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ v1_partfun1(sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),sK0)
    | ~ r2_hidden(sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),k1_tarski(sK3)) ),
    inference(forward_demodulation,[],[f16785,f16704])).

fof(f16785,plain,
    ( ~ m1_subset_1(sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ v1_partfun1(sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),sK0)
    | ~ r2_hidden(sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),k1_tarski(sK3)) ),
    inference(subsumption_resolution,[],[f16784,f65])).

fof(f16784,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ v1_partfun1(sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),sK0)
    | ~ r2_hidden(sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),k1_tarski(sK3)) ),
    inference(forward_demodulation,[],[f16783,f16704])).

fof(f16783,plain,
    ( ~ v1_funct_1(sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)))
    | ~ m1_subset_1(sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ v1_partfun1(sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),sK0)
    | ~ r2_hidden(sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),k1_tarski(sK3)) ),
    inference(subsumption_resolution,[],[f16782,f68])).

fof(f16782,plain,
    ( ~ v1_funct_1(sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)))
    | ~ m1_subset_1(sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ v1_partfun1(sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),sK0)
    | ~ r2_hidden(sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),k1_tarski(sK3))
    | k1_tarski(sK3) = k5_partfun1(sK0,k1_tarski(sK1),sK2) ),
    inference(subsumption_resolution,[],[f16781,f69])).

fof(f16781,plain,
    ( ~ v1_funct_1(sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)))
    | ~ m1_subset_1(sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ v1_partfun1(sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),sK0)
    | ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),k1_tarski(sK3))
    | k1_tarski(sK3) = k5_partfun1(sK0,k1_tarski(sK1),sK2) ),
    inference(subsumption_resolution,[],[f16780,f70])).

fof(f16780,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ v1_funct_1(sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)))
    | ~ m1_subset_1(sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ v1_partfun1(sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),sK0)
    | ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),k1_tarski(sK3))
    | k1_tarski(sK3) = k5_partfun1(sK0,k1_tarski(sK1),sK2) ),
    inference(subsumption_resolution,[],[f16756,f229])).

fof(f229,plain,(
    r1_partfun1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f228,f141])).

fof(f141,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f67,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t164_funct_2.p',cc1_relset_1)).

fof(f228,plain,
    ( ~ v1_relat_1(sK3)
    | r1_partfun1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f227,f69])).

fof(f227,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | r1_partfun1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f226,f162])).

fof(f162,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f70,f108])).

fof(f226,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | r1_partfun1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f224,f65])).

fof(f224,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | r1_partfun1(sK2,sK3) ),
    inference(resolution,[],[f219,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ r1_partfun1(X0,X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | r1_partfun1(X1,X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X1,X0)
      | ~ r1_partfun1(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X1,X0)
      | ~ r1_partfun1(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( r1_partfun1(X0,X1)
       => r1_partfun1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t164_funct_2.p',symmetry_r1_partfun1)).

fof(f219,plain,(
    r1_partfun1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f217,f69])).

fof(f217,plain,
    ( ~ v1_funct_1(sK2)
    | r1_partfun1(sK3,sK2) ),
    inference(resolution,[],[f146,f70])).

fof(f146,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      | ~ v1_funct_1(X0)
      | r1_partfun1(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f135,f65])).

fof(f135,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK3)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      | r1_partfun1(sK3,X0) ) ),
    inference(resolution,[],[f67,f100])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | r1_partfun1(X2,X3) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_1(X3) )
         => r1_partfun1(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t164_funct_2.p',t143_partfun1)).

fof(f16756,plain,
    ( ~ r1_partfun1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ v1_funct_1(sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)))
    | ~ m1_subset_1(sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ v1_partfun1(sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),sK0)
    | ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK5(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),k1_tarski(sK3))
    | k1_tarski(sK3) = k5_partfun1(sK0,k1_tarski(sK1),sK2) ),
    inference(superposition,[],[f120,f16704])).

fof(f120,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_partfun1(X2,sK5(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(sK5(X0,X1,X2,X3))
      | ~ m1_subset_1(sK5(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(sK5(X0,X1,X2,X3),X0)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(sK5(X0,X1,X2,X3),X3)
      | k5_partfun1(X0,X1,X2) = X3 ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK5(X0,X1,X2,X3) != X5
      | ~ v1_partfun1(X5,X0)
      | ~ r1_partfun1(X2,X5)
      | ~ r2_hidden(sK5(X0,X1,X2,X3),X3)
      | k5_partfun1(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
