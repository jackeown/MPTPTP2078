%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1063+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:12 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 418 expanded)
%              Number of leaves         :    5 (  84 expanded)
%              Depth                    :    9
%              Number of atoms          :  212 (2898 expanded)
%              Number of equality atoms :   10 (  47 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f171,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f105,f118,f110,f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(sK7(X0,X1,X2,X3,X4),X5)
      | sP6(X4,X5,X2,X1,X0)
      | ~ sP6(X4,X3,X2,X1,X0) ) ),
    inference(global_subsumption,[],[f28,f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP6(X4,X5,X2,X1,X0)
      | ~ r2_hidden(sK7(X0,X1,X2,X3,X4),X5)
      | ~ m1_subset_1(sK7(X0,X1,X2,X3,X4),k1_zfmisc_1(X0))
      | ~ sP6(X4,X3,X2,X1,X0) ) ),
    inference(superposition,[],[f44,f30])).

fof(f30,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( k7_relset_1(X0,X1,X2,sK7(X0,X1,X2,X3,X5)) = X5
      | ~ sP6(X5,X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( k7_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( ( r2_hidden(X5,X4)
                            <=> ? [X6] :
                                  ( k7_relset_1(X0,X1,X2,X6) = X5
                                  & r2_hidden(X6,X3)
                                  & m1_subset_1(X6,k1_zfmisc_1(X0)) ) )
                            | ~ m1_subset_1(X5,k1_zfmisc_1(X1)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( k7_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( ( r2_hidden(X5,X4)
                            <=> ? [X6] :
                                  ( k7_relset_1(X0,X1,X2,X6) = X5
                                  & r2_hidden(X6,X3)
                                  & m1_subset_1(X6,k1_zfmisc_1(X0)) ) )
                            | ~ m1_subset_1(X5,k1_zfmisc_1(X1)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))
                     => ( k7_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(X1))
                           => ( r2_hidden(X5,X4)
                            <=> ? [X6] :
                                  ( k7_relset_1(X0,X1,X2,X6) = X5
                                  & r2_hidden(X6,X3)
                                  & m1_subset_1(X6,k1_zfmisc_1(X0)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_funct_2)).

fof(f44,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( sP6(k7_relset_1(X0,X1,X2,X6),X3,X2,X1,X0)
      | ~ r2_hidden(X6,X3)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X6,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(X0))
      | ~ r2_hidden(X6,X3)
      | k7_relset_1(X0,X1,X2,X6) != X5
      | sP6(X5,X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3,X5),k1_zfmisc_1(X0))
      | ~ sP6(X5,X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f110,plain,(
    r2_hidden(sK7(sK0,sK1,sK2,sK3,sK8(k7_funct_2(sK0,sK1,sK2,sK3),k7_funct_2(sK0,sK1,sK2,sK4))),sK4) ),
    inference(unit_resulting_resolution,[],[f105,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK7(X3,X2,X1,sK3,X0),sK4)
      | ~ sP6(X0,sK3,X1,X2,X3) ) ),
    inference(resolution,[],[f29,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | r2_hidden(X0,sK4) ) ),
    inference(resolution,[],[f36,f19])).

fof(f19,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r1_tarski(k7_funct_2(X0,X1,X2,X3),k7_funct_2(X0,X1,X2,X4))
                      & r1_tarski(X3,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f8])).

% (26174)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r1_tarski(k7_funct_2(X0,X1,X2,X3),k7_funct_2(X0,X1,X2,X4))
                      & r1_tarski(X3,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X2,X0,X1)
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0)))
                       => ( r1_tarski(X3,X4)
                         => r1_tarski(k7_funct_2(X0,X1,X2,X3),k7_funct_2(X0,X1,X2,X4)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0)))
                     => ( r1_tarski(X3,X4)
                       => r1_tarski(k7_funct_2(X0,X1,X2,X3),k7_funct_2(X0,X1,X2,X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t180_funct_2)).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f29,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(sK7(X0,X1,X2,X3,X5),X3)
      | ~ sP6(X5,X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f118,plain,(
    ~ sP6(sK8(k7_funct_2(sK0,sK1,sK2,sK3),k7_funct_2(sK0,sK1,sK2,sK4)),sK4,sK2,sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f22,f26,f25,f23,f18,f92,f46,f24,f88,f43])).

fof(f43,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
      | ~ sP6(X5,X3,X2,X1,X0)
      | r2_hidden(X5,k7_funct_2(X0,X1,X2,X3)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
      | ~ sP6(X5,X3,X2,X1,X0)
      | r2_hidden(X5,X4)
      | k7_funct_2(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f88,plain,(
    m1_subset_1(k7_funct_2(sK0,sK1,sK2,sK4),k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(unit_resulting_resolution,[],[f26,f22,f25,f18,f23,f24,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_funct_2)).

fof(f24,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f9])).

fof(f46,plain,(
    ~ r2_hidden(sK8(k7_funct_2(sK0,sK1,sK2,sK3),k7_funct_2(sK0,sK1,sK2,sK4)),k7_funct_2(sK0,sK1,sK2,sK4)) ),
    inference(unit_resulting_resolution,[],[f20,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK8(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f20,plain,(
    ~ r1_tarski(k7_funct_2(sK0,sK1,sK2,sK3),k7_funct_2(sK0,sK1,sK2,sK4)) ),
    inference(cnf_transformation,[],[f9])).

fof(f92,plain,(
    m1_subset_1(sK8(k7_funct_2(sK0,sK1,sK2,sK3),k7_funct_2(sK0,sK1,sK2,sK4)),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f45,f89,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f89,plain,(
    m1_subset_1(k7_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(unit_resulting_resolution,[],[f26,f22,f25,f21,f23,f24,f41])).

fof(f21,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f45,plain,(
    r2_hidden(sK8(k7_funct_2(sK0,sK1,sK2,sK3),k7_funct_2(sK0,sK1,sK2,sK4)),k7_funct_2(sK0,sK1,sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f20,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f18,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f23,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f25,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f26,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f22,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f105,plain,(
    sP6(sK8(k7_funct_2(sK0,sK1,sK2,sK3),k7_funct_2(sK0,sK1,sK2,sK4)),sK3,sK2,sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f22,f26,f25,f23,f21,f92,f45,f24,f89,f42])).

fof(f42,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
      | sP6(X5,X3,X2,X1,X0)
      | ~ r2_hidden(X5,k7_funct_2(X0,X1,X2,X3)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
      | sP6(X5,X3,X2,X1,X0)
      | ~ r2_hidden(X5,X4)
      | k7_funct_2(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f11])).

%------------------------------------------------------------------------------
