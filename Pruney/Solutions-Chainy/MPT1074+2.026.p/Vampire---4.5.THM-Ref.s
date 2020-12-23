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
% DateTime   : Thu Dec  3 13:08:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 167 expanded)
%              Number of leaves         :    5 (  30 expanded)
%              Depth                    :   24
%              Number of atoms          :  188 ( 905 expanded)
%              Number of equality atoms :   24 (  30 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f66,plain,(
    $false ),
    inference(subsumption_resolution,[],[f65,f20])).

fof(f20,plain,(
    ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_2(X3,X1,X2)
                  & v1_funct_1(X3) )
               => ( ! [X4] :
                      ( m1_subset_1(X4,X1)
                     => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) )
                 => r1_tarski(k2_relset_1(X1,X2,X3),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(X3,X1,X2)
                & v1_funct_1(X3) )
             => ( ! [X4] :
                    ( m1_subset_1(X4,X1)
                   => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) )
               => r1_tarski(k2_relset_1(X1,X2,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_funct_2)).

fof(f65,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) ),
    inference(resolution,[],[f64,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

% (12283)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f64,plain,(
    r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK0) ),
    inference(subsumption_resolution,[],[f63,f20])).

fof(f63,plain,
    ( r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK0)
    | r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) ),
    inference(subsumption_resolution,[],[f62,f19])).

fof(f19,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f9])).

fof(f62,plain,
    ( r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) ),
    inference(subsumption_resolution,[],[f61,f18])).

fof(f18,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f61,plain,
    ( r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK0)
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) ),
    inference(resolution,[],[f60,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,sK4(k2_relset_1(X0,X1,sK3),X2),sK3),X0)
      | ~ v1_funct_2(sK3,X0,X1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r1_tarski(k2_relset_1(X0,X1,sK3),X2) ) ),
    inference(resolution,[],[f37,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_relset_1(X0,X1,sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK3,X0,X1)
      | r2_hidden(sK5(X0,X2,sK3),X0) ) ),
    inference(resolution,[],[f30,f17])).

fof(f17,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,k2_relset_1(X0,X1,X3))
      | r2_hidden(sK5(X0,X2,X3),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k1_funct_1(X3,X4) = X2
          & r2_hidden(X4,X0) )
      | ~ r2_hidden(X2,k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k1_funct_1(X3,X4) = X2
          & r2_hidden(X4,X0) )
      | ~ r2_hidden(X2,k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ~ ( k1_funct_1(X3,X4) = X2
                & r2_hidden(X4,X0) )
          & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_2)).

fof(f60,plain,
    ( ~ r2_hidden(sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK3),sK1)
    | r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK0) ),
    inference(subsumption_resolution,[],[f59,f22])).

fof(f22,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f59,plain,
    ( r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK0)
    | ~ r2_hidden(sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK3),sK1)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f58,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f58,plain,
    ( ~ m1_subset_1(sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK3),sK1)
    | r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK0) ),
    inference(superposition,[],[f16,f57])).

fof(f57,plain,(
    sK4(k2_relset_1(sK1,sK2,sK3),sK0) = k3_funct_2(sK1,sK2,sK3,sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK3)) ),
    inference(forward_demodulation,[],[f56,f53])).

fof(f53,plain,(
    sK4(k2_relset_1(sK1,sK2,sK3),sK0) = k1_funct_1(sK3,sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK3)) ),
    inference(resolution,[],[f51,f20])).

fof(f51,plain,(
    ! [X0] :
      ( r1_tarski(k2_relset_1(sK1,sK2,sK3),X0)
      | sK4(k2_relset_1(sK1,sK2,sK3),X0) = k1_funct_1(sK3,sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),X0),sK3)) ) ),
    inference(resolution,[],[f50,f27])).

fof(f50,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relset_1(sK1,sK2,sK3))
      | k1_funct_1(sK3,sK5(sK1,X0,sK3)) = X0 ) ),
    inference(subsumption_resolution,[],[f49,f19])).

fof(f49,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ r2_hidden(X0,k2_relset_1(sK1,sK2,sK3))
      | k1_funct_1(sK3,sK5(sK1,X0,sK3)) = X0 ) ),
    inference(resolution,[],[f48,f18])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(sK3,X0,X1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,k2_relset_1(X0,X1,sK3))
      | k1_funct_1(sK3,sK5(X0,X2,sK3)) = X2 ) ),
    inference(resolution,[],[f31,f17])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,k2_relset_1(X0,X1,X3))
      | k1_funct_1(X3,sK5(X0,X2,X3)) = X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f56,plain,(
    k1_funct_1(sK3,sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK3)) = k3_funct_2(sK1,sK2,sK3,sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK3)) ),
    inference(resolution,[],[f55,f20])).

fof(f55,plain,(
    ! [X0] :
      ( r1_tarski(k2_relset_1(sK1,sK2,sK3),X0)
      | k1_funct_1(sK3,sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),X0),sK3)) = k3_funct_2(sK1,sK2,sK3,sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),X0),sK3)) ) ),
    inference(subsumption_resolution,[],[f54,f19])).

fof(f54,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),X0),sK3)) = k3_funct_2(sK1,sK2,sK3,sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),X0),sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | r1_tarski(k2_relset_1(sK1,sK2,sK3),X0) ) ),
    inference(resolution,[],[f47,f18])).

fof(f47,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(sK3,sK1,X1)
      | k3_funct_2(sK1,sK2,sK3,sK5(sK1,sK4(k2_relset_1(sK1,X1,sK3),X2),sK3)) = k1_funct_1(sK3,sK5(sK1,sK4(k2_relset_1(sK1,X1,sK3),X2),sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | r1_tarski(k2_relset_1(sK1,X1,sK3),X2) ) ),
    inference(resolution,[],[f45,f38])).

fof(f45,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f44,f22])).

fof(f44,plain,(
    ! [X0] :
      ( k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0)
      | ~ r2_hidden(X0,sK1)
      | v1_xboole_0(sK1) ) ),
    inference(resolution,[],[f43,f25])).

fof(f43,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f42,f19])).

fof(f42,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ m1_subset_1(X0,sK1)
      | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f41,f22])).

fof(f41,plain,(
    ! [X0] :
      ( v1_xboole_0(sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ m1_subset_1(X0,sK1)
      | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0) ) ),
    inference(resolution,[],[f40,f18])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(sK3,X0,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,X0)
      | k3_funct_2(X0,X1,sK3,X2) = k1_funct_1(sK3,X2) ) ),
    inference(resolution,[],[f29,f17])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | v1_xboole_0(X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f13])).

% (12294)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f16,plain,(
    ! [X4] :
      ( r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0)
      | ~ m1_subset_1(X4,sK1) ) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:23:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.54  % (12292)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.55  % (12278)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.56  % (12286)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.56  % (12284)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.56  % (12284)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 0.20/0.57  % (12302)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.57  % SZS output start Proof for theBenchmark
% 0.20/0.57  fof(f66,plain,(
% 0.20/0.57    $false),
% 0.20/0.57    inference(subsumption_resolution,[],[f65,f20])).
% 0.20/0.57  fof(f20,plain,(
% 0.20/0.57    ~r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)),
% 0.20/0.57    inference(cnf_transformation,[],[f9])).
% 0.20/0.57  fof(f9,plain,(
% 0.20/0.57    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 0.20/0.57    inference(flattening,[],[f8])).
% 0.20/0.57  fof(f8,plain,(
% 0.20/0.57    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 0.20/0.57    inference(ennf_transformation,[],[f6])).
% 0.20/0.57  fof(f6,negated_conjecture,(
% 0.20/0.57    ~! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 0.20/0.57    inference(negated_conjecture,[],[f5])).
% 0.20/0.57  fof(f5,conjecture,(
% 0.20/0.57    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_funct_2)).
% 0.20/0.57  fof(f65,plain,(
% 0.20/0.57    r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)),
% 0.20/0.57    inference(resolution,[],[f64,f28])).
% 0.20/0.57  fof(f28,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f11])).
% 0.20/0.57  fof(f11,plain,(
% 0.20/0.57    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f7])).
% 0.20/0.57  fof(f7,plain,(
% 0.20/0.57    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 0.20/0.57    inference(unused_predicate_definition_removal,[],[f1])).
% 0.20/0.57  % (12283)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.57  fof(f1,axiom,(
% 0.20/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.57  fof(f64,plain,(
% 0.20/0.57    r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK0)),
% 0.20/0.57    inference(subsumption_resolution,[],[f63,f20])).
% 0.20/0.57  fof(f63,plain,(
% 0.20/0.57    r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK0) | r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)),
% 0.20/0.57    inference(subsumption_resolution,[],[f62,f19])).
% 0.20/0.57  fof(f19,plain,(
% 0.20/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.57    inference(cnf_transformation,[],[f9])).
% 0.20/0.57  fof(f62,plain,(
% 0.20/0.57    r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)),
% 0.20/0.57    inference(subsumption_resolution,[],[f61,f18])).
% 0.20/0.57  fof(f18,plain,(
% 0.20/0.57    v1_funct_2(sK3,sK1,sK2)),
% 0.20/0.57    inference(cnf_transformation,[],[f9])).
% 0.20/0.57  fof(f61,plain,(
% 0.20/0.57    r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK0) | ~v1_funct_2(sK3,sK1,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)),
% 0.20/0.57    inference(resolution,[],[f60,f38])).
% 0.20/0.57  fof(f38,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,sK4(k2_relset_1(X0,X1,sK3),X2),sK3),X0) | ~v1_funct_2(sK3,X0,X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r1_tarski(k2_relset_1(X0,X1,sK3),X2)) )),
% 0.20/0.57    inference(resolution,[],[f37,f27])).
% 0.20/0.57  fof(f27,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f11])).
% 0.20/0.57  fof(f37,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_relset_1(X0,X1,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK3,X0,X1) | r2_hidden(sK5(X0,X2,sK3),X0)) )),
% 0.20/0.57    inference(resolution,[],[f30,f17])).
% 0.20/0.57  fof(f17,plain,(
% 0.20/0.57    v1_funct_1(sK3)),
% 0.20/0.57    inference(cnf_transformation,[],[f9])).
% 0.20/0.57  fof(f30,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,k2_relset_1(X0,X1,X3)) | r2_hidden(sK5(X0,X2,X3),X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f15])).
% 0.20/0.57  fof(f15,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : (? [X4] : (k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) | ~r2_hidden(X2,k2_relset_1(X0,X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.20/0.57    inference(flattening,[],[f14])).
% 0.20/0.57  fof(f14,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : ((? [X4] : (k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) | ~r2_hidden(X2,k2_relset_1(X0,X1,X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.20/0.57    inference(ennf_transformation,[],[f4])).
% 0.20/0.57  fof(f4,axiom,(
% 0.20/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ~(! [X4] : ~(k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_2)).
% 0.20/0.57  fof(f60,plain,(
% 0.20/0.57    ~r2_hidden(sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK3),sK1) | r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK0)),
% 0.20/0.57    inference(subsumption_resolution,[],[f59,f22])).
% 0.20/0.57  fof(f22,plain,(
% 0.20/0.57    ~v1_xboole_0(sK1)),
% 0.20/0.57    inference(cnf_transformation,[],[f9])).
% 0.20/0.57  fof(f59,plain,(
% 0.20/0.57    r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK0) | ~r2_hidden(sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK3),sK1) | v1_xboole_0(sK1)),
% 0.20/0.57    inference(resolution,[],[f58,f25])).
% 0.20/0.57  fof(f25,plain,(
% 0.20/0.57    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f10])).
% 0.20/0.57  fof(f10,plain,(
% 0.20/0.57    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f2])).
% 0.20/0.57  fof(f2,axiom,(
% 0.20/0.57    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.57  fof(f58,plain,(
% 0.20/0.57    ~m1_subset_1(sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK3),sK1) | r2_hidden(sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK0)),
% 0.20/0.57    inference(superposition,[],[f16,f57])).
% 0.20/0.57  fof(f57,plain,(
% 0.20/0.57    sK4(k2_relset_1(sK1,sK2,sK3),sK0) = k3_funct_2(sK1,sK2,sK3,sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK3))),
% 0.20/0.57    inference(forward_demodulation,[],[f56,f53])).
% 0.20/0.57  fof(f53,plain,(
% 0.20/0.57    sK4(k2_relset_1(sK1,sK2,sK3),sK0) = k1_funct_1(sK3,sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK3))),
% 0.20/0.57    inference(resolution,[],[f51,f20])).
% 0.20/0.57  fof(f51,plain,(
% 0.20/0.57    ( ! [X0] : (r1_tarski(k2_relset_1(sK1,sK2,sK3),X0) | sK4(k2_relset_1(sK1,sK2,sK3),X0) = k1_funct_1(sK3,sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),X0),sK3))) )),
% 0.20/0.57    inference(resolution,[],[f50,f27])).
% 0.20/0.57  fof(f50,plain,(
% 0.20/0.57    ( ! [X0] : (~r2_hidden(X0,k2_relset_1(sK1,sK2,sK3)) | k1_funct_1(sK3,sK5(sK1,X0,sK3)) = X0) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f49,f19])).
% 0.20/0.57  fof(f49,plain,(
% 0.20/0.57    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~r2_hidden(X0,k2_relset_1(sK1,sK2,sK3)) | k1_funct_1(sK3,sK5(sK1,X0,sK3)) = X0) )),
% 0.20/0.57    inference(resolution,[],[f48,f18])).
% 0.20/0.57  fof(f48,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~v1_funct_2(sK3,X0,X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,k2_relset_1(X0,X1,sK3)) | k1_funct_1(sK3,sK5(X0,X2,sK3)) = X2) )),
% 0.20/0.57    inference(resolution,[],[f31,f17])).
% 0.20/0.57  fof(f31,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,k2_relset_1(X0,X1,X3)) | k1_funct_1(X3,sK5(X0,X2,X3)) = X2) )),
% 0.20/0.57    inference(cnf_transformation,[],[f15])).
% 0.20/0.57  fof(f56,plain,(
% 0.20/0.57    k1_funct_1(sK3,sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK3)) = k3_funct_2(sK1,sK2,sK3,sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),sK0),sK3))),
% 0.20/0.57    inference(resolution,[],[f55,f20])).
% 0.20/0.57  fof(f55,plain,(
% 0.20/0.57    ( ! [X0] : (r1_tarski(k2_relset_1(sK1,sK2,sK3),X0) | k1_funct_1(sK3,sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),X0),sK3)) = k3_funct_2(sK1,sK2,sK3,sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),X0),sK3))) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f54,f19])).
% 0.20/0.57  fof(f54,plain,(
% 0.20/0.57    ( ! [X0] : (k1_funct_1(sK3,sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),X0),sK3)) = k3_funct_2(sK1,sK2,sK3,sK5(sK1,sK4(k2_relset_1(sK1,sK2,sK3),X0),sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | r1_tarski(k2_relset_1(sK1,sK2,sK3),X0)) )),
% 0.20/0.57    inference(resolution,[],[f47,f18])).
% 0.20/0.57  fof(f47,plain,(
% 0.20/0.57    ( ! [X2,X1] : (~v1_funct_2(sK3,sK1,X1) | k3_funct_2(sK1,sK2,sK3,sK5(sK1,sK4(k2_relset_1(sK1,X1,sK3),X2),sK3)) = k1_funct_1(sK3,sK5(sK1,sK4(k2_relset_1(sK1,X1,sK3),X2),sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | r1_tarski(k2_relset_1(sK1,X1,sK3),X2)) )),
% 0.20/0.57    inference(resolution,[],[f45,f38])).
% 0.20/0.57  fof(f45,plain,(
% 0.20/0.57    ( ! [X0] : (~r2_hidden(X0,sK1) | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0)) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f44,f22])).
% 0.20/0.57  fof(f44,plain,(
% 0.20/0.57    ( ! [X0] : (k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0) | ~r2_hidden(X0,sK1) | v1_xboole_0(sK1)) )),
% 0.20/0.57    inference(resolution,[],[f43,f25])).
% 0.20/0.57  fof(f43,plain,(
% 0.20/0.57    ( ! [X0] : (~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0)) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f42,f19])).
% 0.20/0.57  fof(f42,plain,(
% 0.20/0.57    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0)) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f41,f22])).
% 0.20/0.57  fof(f41,plain,(
% 0.20/0.57    ( ! [X0] : (v1_xboole_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0)) )),
% 0.20/0.57    inference(resolution,[],[f40,f18])).
% 0.20/0.57  fof(f40,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~v1_funct_2(sK3,X0,X1) | v1_xboole_0(X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,X0) | k3_funct_2(X0,X1,sK3,X2) = k1_funct_1(sK3,X2)) )),
% 0.20/0.57    inference(resolution,[],[f29,f17])).
% 0.20/0.57  fof(f29,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | v1_xboole_0(X0) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f13])).
% 0.20/0.57  % (12294)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.57  fof(f13,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.20/0.57    inference(flattening,[],[f12])).
% 0.20/0.58  fof(f12,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f3])).
% 0.20/0.58  fof(f3,axiom,(
% 0.20/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.20/0.58  fof(f16,plain,(
% 0.20/0.58    ( ! [X4] : (r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0) | ~m1_subset_1(X4,sK1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f9])).
% 0.20/0.58  % SZS output end Proof for theBenchmark
% 0.20/0.58  % (12284)------------------------------
% 0.20/0.58  % (12284)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (12284)Termination reason: Refutation
% 0.20/0.58  
% 0.20/0.58  % (12284)Memory used [KB]: 6268
% 0.20/0.58  % (12284)Time elapsed: 0.153 s
% 0.20/0.58  % (12284)------------------------------
% 0.20/0.58  % (12284)------------------------------
% 0.20/0.58  % (12277)Success in time 0.227 s
%------------------------------------------------------------------------------
