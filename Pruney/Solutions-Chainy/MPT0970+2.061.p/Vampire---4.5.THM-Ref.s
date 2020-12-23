%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:57 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 141 expanded)
%              Number of leaves         :   12 (  29 expanded)
%              Depth                    :   18
%              Number of atoms          :  194 ( 619 expanded)
%              Number of equality atoms :   65 ( 186 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f122,plain,(
    $false ),
    inference(subsumption_resolution,[],[f119,f46])).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f119,plain,(
    ~ r1_tarski(k1_xboole_0,k2_relset_1(sK0,k1_xboole_0,sK2)) ),
    inference(backward_demodulation,[],[f83,f104])).

fof(f104,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f103,f29])).

fof(f29,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( ! [X4] :
                    ~ ( k1_funct_1(X2,X4) = X3
                      & r2_hidden(X4,X0) )
                & r2_hidden(X3,X1) )
         => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

fof(f103,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f102,f28])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f102,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | sK1 = k2_relset_1(X0,sK1,sK2)
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f91,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ sP7(X2,X1)
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(general_splitting,[],[f31,f62_D])).

fof(f62,plain,(
    ! [X4,X2,X1] :
      ( ~ r2_hidden(k4_tarski(X4,sK4(X1,X2)),X2)
      | sP7(X2,X1) ) ),
    inference(cnf_transformation,[],[f62_D])).

fof(f62_D,plain,(
    ! [X1,X2] :
      ( ! [X4] : ~ r2_hidden(k4_tarski(X4,sK4(X1,X2)),X2)
    <=> ~ sP7(X2,X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ r2_hidden(k4_tarski(X4,sK4(X1,X2)),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relset_1)).

fof(f91,plain,
    ( sP7(sK2,sK1)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f90,f62])).

fof(f90,plain,
    ( r2_hidden(k4_tarski(sK3(sK4(sK1,sK2)),sK4(sK1,sK2)),sK2)
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f89,f76])).

fof(f76,plain,(
    sK4(sK1,sK2) = k1_funct_1(sK2,sK3(sK4(sK1,sK2))) ),
    inference(resolution,[],[f25,f73])).

fof(f73,plain,(
    r2_hidden(sK4(sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f69,f29])).

fof(f69,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | r2_hidden(sK4(sK1,sK2),sK1) ),
    inference(resolution,[],[f28,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = X1
      | r2_hidden(sK4(X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f25,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | k1_funct_1(sK2,sK3(X3)) = X3 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f89,plain,
    ( r2_hidden(k4_tarski(sK3(sK4(sK1,sK2)),k1_funct_1(sK2,sK3(sK4(sK1,sK2)))),sK2)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f88,f75])).

fof(f75,plain,(
    r2_hidden(sK3(sK4(sK1,sK2)),sK0) ),
    inference(resolution,[],[f73,f24])).

fof(f24,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | r2_hidden(sK3(X3),sK0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f88,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2)
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f87,f74])).

fof(f74,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f72,f44])).

fof(f44,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f72,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f28,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f87,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | ~ v1_relat_1(sK2)
      | r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2)
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f86,f26])).

fof(f26,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f86,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2)
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f52,f84])).

fof(f84,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f66,f65])).

fof(f65,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f64,f28])).

fof(f64,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f27,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f27,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f66,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f28,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | k1_funct_1(X2,X0) != X1
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f83,plain,(
    ~ r1_tarski(sK1,k2_relset_1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f81,f29])).

fof(f81,plain,
    ( ~ r1_tarski(sK1,k2_relset_1(sK0,sK1,sK2))
    | sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f79,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f79,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK2),sK1) ),
    inference(resolution,[],[f68,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f68,plain,(
    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f28,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:12:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (15363)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.52  % (15372)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.52  % (15368)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.52  % (15387)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.52  % (15366)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (15378)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (15377)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (15376)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.53  % (15369)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.53  % (15375)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.53  % (15369)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (15388)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.53  % (15385)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.53  % (15370)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.53  % (15370)Refutation not found, incomplete strategy% (15370)------------------------------
% 0.22/0.53  % (15370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (15370)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (15370)Memory used [KB]: 10618
% 0.22/0.53  % (15370)Time elapsed: 0.109 s
% 0.22/0.53  % (15370)------------------------------
% 0.22/0.53  % (15370)------------------------------
% 0.22/0.54  % (15386)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.54  % (15382)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.54  % (15364)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (15365)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.54  % (15380)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.54  % (15374)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f122,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(subsumption_resolution,[],[f119,f46])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.54  fof(f119,plain,(
% 0.22/0.54    ~r1_tarski(k1_xboole_0,k2_relset_1(sK0,k1_xboole_0,sK2))),
% 0.22/0.54    inference(backward_demodulation,[],[f83,f104])).
% 0.22/0.54  fof(f104,plain,(
% 0.22/0.54    k1_xboole_0 = sK1),
% 0.22/0.54    inference(subsumption_resolution,[],[f103,f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.54    inference(flattening,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.22/0.54    inference(negated_conjecture,[],[f12])).
% 0.22/0.54  fof(f12,conjecture,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).
% 0.22/0.54  fof(f103,plain,(
% 0.22/0.54    sK1 = k2_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1),
% 0.22/0.54    inference(resolution,[],[f102,f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f102,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | sK1 = k2_relset_1(X0,sK1,sK2) | k1_xboole_0 = sK1) )),
% 0.22/0.54    inference(resolution,[],[f91,f63])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~sP7(X2,X1) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(general_splitting,[],[f31,f62_D])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    ( ! [X4,X2,X1] : (~r2_hidden(k4_tarski(X4,sK4(X1,X2)),X2) | sP7(X2,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f62_D])).
% 0.22/0.54  fof(f62_D,plain,(
% 0.22/0.54    ( ! [X1,X2] : (( ! [X4] : ~r2_hidden(k4_tarski(X4,sK4(X1,X2)),X2) ) <=> ~sP7(X2,X1)) )),
% 0.22/0.54    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = X1 | ~r2_hidden(k4_tarski(X4,sK4(X1,X2)),X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relset_1)).
% 0.22/0.54  fof(f91,plain,(
% 0.22/0.54    sP7(sK2,sK1) | k1_xboole_0 = sK1),
% 0.22/0.54    inference(resolution,[],[f90,f62])).
% 0.22/0.54  fof(f90,plain,(
% 0.22/0.54    r2_hidden(k4_tarski(sK3(sK4(sK1,sK2)),sK4(sK1,sK2)),sK2) | k1_xboole_0 = sK1),
% 0.22/0.54    inference(forward_demodulation,[],[f89,f76])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    sK4(sK1,sK2) = k1_funct_1(sK2,sK3(sK4(sK1,sK2)))),
% 0.22/0.54    inference(resolution,[],[f25,f73])).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    r2_hidden(sK4(sK1,sK2),sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f69,f29])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    sK1 = k2_relset_1(sK0,sK1,sK2) | r2_hidden(sK4(sK1,sK2),sK1)),
% 0.22/0.54    inference(resolution,[],[f28,f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = X1 | r2_hidden(sK4(X1,X2),X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ( ! [X3] : (~r2_hidden(X3,sK1) | k1_funct_1(sK2,sK3(X3)) = X3) )),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f89,plain,(
% 0.22/0.54    r2_hidden(k4_tarski(sK3(sK4(sK1,sK2)),k1_funct_1(sK2,sK3(sK4(sK1,sK2)))),sK2) | k1_xboole_0 = sK1),
% 0.22/0.54    inference(resolution,[],[f88,f75])).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    r2_hidden(sK3(sK4(sK1,sK2)),sK0)),
% 0.22/0.54    inference(resolution,[],[f73,f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ( ! [X3] : (~r2_hidden(X3,sK1) | r2_hidden(sK3(X3),sK0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f88,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2) | k1_xboole_0 = sK1) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f87,f74])).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    v1_relat_1(sK2)),
% 0.22/0.54    inference(subsumption_resolution,[],[f72,f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2)),
% 0.22/0.54    inference(resolution,[],[f28,f45])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.54  fof(f87,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,sK0) | ~v1_relat_1(sK2) | r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2) | k1_xboole_0 = sK1) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f86,f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    v1_funct_1(sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2) | k1_xboole_0 = sK1) )),
% 0.22/0.54    inference(superposition,[],[f52,f84])).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 0.22/0.54    inference(superposition,[],[f66,f65])).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1),
% 0.22/0.54    inference(subsumption_resolution,[],[f64,f28])).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.54    inference(resolution,[],[f27,f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(flattening,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.22/0.54    inference(resolution,[],[f28,f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ( ! [X2,X0] : (~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)) )),
% 0.22/0.54    inference(equality_resolution,[],[f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | k1_funct_1(X2,X0) != X1 | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.54    inference(flattening,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.22/0.54  fof(f83,plain,(
% 0.22/0.54    ~r1_tarski(sK1,k2_relset_1(sK0,sK1,sK2))),
% 0.22/0.54    inference(subsumption_resolution,[],[f81,f29])).
% 0.22/0.54  fof(f81,plain,(
% 0.22/0.54    ~r1_tarski(sK1,k2_relset_1(sK0,sK1,sK2)) | sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.54    inference(resolution,[],[f79,f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    r1_tarski(k2_relset_1(sK0,sK1,sK2),sK1)),
% 0.22/0.54    inference(resolution,[],[f68,f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))),
% 0.22/0.54    inference(resolution,[],[f28,f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (15369)------------------------------
% 0.22/0.54  % (15369)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (15369)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (15369)Memory used [KB]: 6140
% 0.22/0.54  % (15369)Time elapsed: 0.098 s
% 0.22/0.54  % (15369)------------------------------
% 0.22/0.54  % (15369)------------------------------
% 0.22/0.54  % (15362)Success in time 0.173 s
%------------------------------------------------------------------------------
