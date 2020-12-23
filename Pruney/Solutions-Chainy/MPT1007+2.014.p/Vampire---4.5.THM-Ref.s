%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 692 expanded)
%              Number of leaves         :   21 ( 177 expanded)
%              Depth                    :   18
%              Number of atoms          :  267 (2568 expanded)
%              Number of equality atoms :   62 ( 542 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f393,plain,(
    $false ),
    inference(resolution,[],[f388,f65])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f7,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f7,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f388,plain,(
    ! [X0] : ~ m1_subset_1(X0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f381,f378])).

fof(f378,plain,(
    k1_xboole_0 = k1_tarski(sK0) ),
    inference(resolution,[],[f365,f64])).

fof(f64,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

fof(f365,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f364,f357])).

fof(f357,plain,(
    ~ r2_hidden(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f324,f297])).

fof(f297,plain,(
    ! [X0] : k1_xboole_0 = k1_funct_1(k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f296,f200])).

fof(f200,plain,(
    ! [X4] : ~ r2_hidden(X4,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f196,f56])).

% (29821)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f56,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f196,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_mcart_1(X4)) ) ),
    inference(resolution,[],[f182,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f182,plain,(
    ! [X1] :
      ( r2_hidden(k1_mcart_1(X1),k1_xboole_0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f72,f181])).

fof(f181,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f143,f56])).

fof(f143,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X6,k1_mcart_1(sK3(k2_zfmisc_1(X6,X7))))
      | k1_xboole_0 = k2_zfmisc_1(X6,X7) ) ),
    inference(resolution,[],[f90,f70])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_mcart_1(sK3(k2_zfmisc_1(X0,X1))),X0)
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(resolution,[],[f72,f64])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f296,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_xboole_0)
      | k1_xboole_0 = k1_funct_1(k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f295,f54])).

fof(f54,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f295,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_funct_1(k1_xboole_0,X0)
      | r2_hidden(X0,k1_relat_1(k1_xboole_0)) ) ),
    inference(subsumption_resolution,[],[f293,f87])).

fof(f87,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f74,f57])).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f293,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_funct_1(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0)
      | r2_hidden(X0,k1_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[],[f126,f53])).

fof(f53,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f126,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X2)
      | k1_xboole_0 = k1_funct_1(X2,X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(X1,k1_relat_1(X2)) ) ),
    inference(resolution,[],[f79,f59])).

fof(f59,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(X1,k1_relat_1(X0))
      | k1_xboole_0 = k1_funct_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | k1_xboole_0 != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

% (29819)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f324,plain,(
    ~ r2_hidden(k1_funct_1(k1_xboole_0,sK0),sK1) ),
    inference(backward_demodulation,[],[f52,f320])).

% (29825)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f320,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f117,f316])).

fof(f316,plain,(
    ~ r2_hidden(sK0,k1_tarski(sK0)) ),
    inference(resolution,[],[f315,f52])).

fof(f315,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,X0),sK1)
      | ~ r2_hidden(X0,k1_tarski(sK0)) ) ),
    inference(subsumption_resolution,[],[f314,f48])).

fof(f48,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK2,k1_tarski(sK0),sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f41])).

fof(f41,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
      & k1_xboole_0 != sK1
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK2,k1_tarski(sK0),sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

fof(f314,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK0))
      | r2_hidden(k1_funct_1(sK2,X0),sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f313,f50])).

fof(f50,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f313,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      | r2_hidden(k1_funct_1(sK2,X0),sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f312,f51])).

fof(f51,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f42])).

fof(f312,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | ~ r2_hidden(X0,k1_tarski(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      | r2_hidden(k1_funct_1(sK2,X0),sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f78,f49])).

fof(f49,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X3,X0,X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(k1_funct_1(X3,X2),X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

fof(f117,plain,
    ( r2_hidden(sK0,k1_tarski(sK0))
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,
    ( r2_hidden(sK0,k1_tarski(sK0))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f106,f104])).

fof(f104,plain,
    ( sK0 = k1_mcart_1(sK3(sK2))
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f103,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
      | k1_mcart_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 )
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

fof(f103,plain,
    ( r2_hidden(sK3(sK2),k2_zfmisc_1(k1_tarski(sK0),sK1))
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f95,f50])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r2_hidden(sK3(X0),X1)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f69,f64])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f106,plain,
    ( r2_hidden(k1_mcart_1(sK3(sK2)),k1_tarski(sK0))
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f103,f72])).

fof(f52,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f364,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,sK1)
      | ~ r2_hidden(X0,k1_tarski(sK0)) ) ),
    inference(forward_demodulation,[],[f356,f297])).

fof(f356,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,X0),sK1)
      | ~ r2_hidden(X0,k1_tarski(sK0)) ) ),
    inference(backward_demodulation,[],[f315,f320])).

fof(f381,plain,(
    ! [X0] : ~ m1_subset_1(X0,k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f373,f82])).

fof(f82,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(superposition,[],[f66,f58])).

fof(f58,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f66,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_xboole_0)).

% (29811)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f373,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_tarski(sK0))
      | ~ m1_subset_1(X0,k1_tarski(sK0)) ) ),
    inference(resolution,[],[f365,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:05:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (29824)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.51  % (29816)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.51  % (29808)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (29806)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (29805)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (29804)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (29807)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (29823)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (29801)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (29802)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (29815)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (29803)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (29822)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (29808)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % (29810)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (29829)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (29828)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f393,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(resolution,[],[f388,f65])).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(sK4(X0),X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ! [X0] : m1_subset_1(sK4(X0),X0)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f7,f46])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK4(X0),X0))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.22/0.54  fof(f388,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_xboole_0)) )),
% 0.22/0.54    inference(backward_demodulation,[],[f381,f378])).
% 0.22/0.54  fof(f378,plain,(
% 0.22/0.54    k1_xboole_0 = k1_tarski(sK0)),
% 0.22/0.54    inference(resolution,[],[f365,f64])).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f45])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.54    inference(ennf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.54    inference(pure_predicate_removal,[],[f19])).
% 0.22/0.54  fof(f19,axiom,(
% 0.22/0.54    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).
% 0.22/0.54  fof(f365,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f364,f357])).
% 0.22/0.54  fof(f357,plain,(
% 0.22/0.54    ~r2_hidden(k1_xboole_0,sK1)),
% 0.22/0.54    inference(forward_demodulation,[],[f324,f297])).
% 0.22/0.54  fof(f297,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k1_funct_1(k1_xboole_0,X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f296,f200])).
% 0.22/0.54  fof(f200,plain,(
% 0.22/0.54    ( ! [X4] : (~r2_hidden(X4,k1_xboole_0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f196,f56])).
% 0.22/0.54  % (29821)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.54  fof(f196,plain,(
% 0.22/0.54    ( ! [X4] : (~r2_hidden(X4,k1_xboole_0) | ~r1_tarski(k1_xboole_0,k1_mcart_1(X4))) )),
% 0.22/0.54    inference(resolution,[],[f182,f70])).
% 0.22/0.54  fof(f70,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,axiom,(
% 0.22/0.54    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.54  fof(f182,plain,(
% 0.22/0.54    ( ! [X1] : (r2_hidden(k1_mcart_1(X1),k1_xboole_0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 0.22/0.54    inference(superposition,[],[f72,f181])).
% 0.22/0.54  fof(f181,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)) )),
% 0.22/0.54    inference(resolution,[],[f143,f56])).
% 0.22/0.54  fof(f143,plain,(
% 0.22/0.54    ( ! [X6,X7] : (~r1_tarski(X6,k1_mcart_1(sK3(k2_zfmisc_1(X6,X7)))) | k1_xboole_0 = k2_zfmisc_1(X6,X7)) )),
% 0.22/0.54    inference(resolution,[],[f90,f70])).
% 0.22/0.54  fof(f90,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(k1_mcart_1(sK3(k2_zfmisc_1(X0,X1))),X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.22/0.54    inference(resolution,[],[f72,f64])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.22/0.54  fof(f296,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(X0,k1_xboole_0) | k1_xboole_0 = k1_funct_1(k1_xboole_0,X0)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f295,f54])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.54  fof(f295,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k1_funct_1(k1_xboole_0,X0) | r2_hidden(X0,k1_relat_1(k1_xboole_0))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f293,f87])).
% 0.22/0.54  fof(f87,plain,(
% 0.22/0.54    v1_relat_1(k1_xboole_0)),
% 0.22/0.54    inference(resolution,[],[f74,f57])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.54  fof(f293,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k1_funct_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0) | r2_hidden(X0,k1_relat_1(k1_xboole_0))) )),
% 0.22/0.54    inference(resolution,[],[f126,f53])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    v1_xboole_0(k1_xboole_0)),
% 0.22/0.54    inference(cnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    v1_xboole_0(k1_xboole_0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.54  fof(f126,plain,(
% 0.22/0.54    ( ! [X2,X1] : (~v1_xboole_0(X2) | k1_xboole_0 = k1_funct_1(X2,X1) | ~v1_relat_1(X2) | r2_hidden(X1,k1_relat_1(X2))) )),
% 0.22/0.54    inference(resolution,[],[f79,f59])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,axiom,(
% 0.22/0.54    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_funct_1(X0) | r2_hidden(X1,k1_relat_1(X0)) | k1_xboole_0 = k1_funct_1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(equality_resolution,[],[f63])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2 | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(flattening,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,axiom,(
% 0.22/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).
% 0.22/0.54  % (29819)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  fof(f324,plain,(
% 0.22/0.54    ~r2_hidden(k1_funct_1(k1_xboole_0,sK0),sK1)),
% 0.22/0.54    inference(backward_demodulation,[],[f52,f320])).
% 0.22/0.54  % (29825)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  fof(f320,plain,(
% 0.22/0.54    k1_xboole_0 = sK2),
% 0.22/0.54    inference(subsumption_resolution,[],[f117,f316])).
% 0.22/0.54  fof(f316,plain,(
% 0.22/0.54    ~r2_hidden(sK0,k1_tarski(sK0))),
% 0.22/0.54    inference(resolution,[],[f315,f52])).
% 0.22/0.54  fof(f315,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),sK1) | ~r2_hidden(X0,k1_tarski(sK0))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f314,f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    v1_funct_1(sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK2,sK0),sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.22/0.55    inference(flattening,[],[f24])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.22/0.55    inference(ennf_transformation,[],[f22])).
% 0.22/0.55  fof(f22,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.22/0.55    inference(negated_conjecture,[],[f21])).
% 0.22/0.55  fof(f21,conjecture,(
% 0.22/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).
% 0.22/0.55  fof(f314,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0)) | r2_hidden(k1_funct_1(sK2,X0),sK1) | ~v1_funct_1(sK2)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f313,f50])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.22/0.55    inference(cnf_transformation,[],[f42])).
% 0.22/0.55  fof(f313,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) | r2_hidden(k1_funct_1(sK2,X0),sK1) | ~v1_funct_1(sK2)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f312,f51])).
% 0.22/0.55  fof(f51,plain,(
% 0.22/0.55    k1_xboole_0 != sK1),
% 0.22/0.55    inference(cnf_transformation,[],[f42])).
% 0.22/0.55  fof(f312,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = sK1 | ~r2_hidden(X0,k1_tarski(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) | r2_hidden(k1_funct_1(sK2,X0),sK1) | ~v1_funct_1(sK2)) )),
% 0.22/0.55    inference(resolution,[],[f78,f49])).
% 0.22/0.55  fof(f49,plain,(
% 0.22/0.55    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f42])).
% 0.22/0.55  fof(f78,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X3,X0,X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(k1_funct_1(X3,X2),X1) | ~v1_funct_1(X3)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f40])).
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.55    inference(flattening,[],[f39])).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.55    inference(ennf_transformation,[],[f20])).
% 0.22/0.55  fof(f20,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).
% 0.22/0.55  fof(f117,plain,(
% 0.22/0.55    r2_hidden(sK0,k1_tarski(sK0)) | k1_xboole_0 = sK2),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f116])).
% 0.22/0.55  fof(f116,plain,(
% 0.22/0.55    r2_hidden(sK0,k1_tarski(sK0)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 0.22/0.55    inference(superposition,[],[f106,f104])).
% 0.22/0.55  fof(f104,plain,(
% 0.22/0.55    sK0 = k1_mcart_1(sK3(sK2)) | k1_xboole_0 = sK2),
% 0.22/0.55    inference(resolution,[],[f103,f75])).
% 0.22/0.55  fof(f75,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) | k1_mcart_1(X0) = X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f36])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1) | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 0.22/0.55    inference(ennf_transformation,[],[f18])).
% 0.22/0.55  fof(f18,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).
% 0.22/0.55  fof(f103,plain,(
% 0.22/0.55    r2_hidden(sK3(sK2),k2_zfmisc_1(k1_tarski(sK0),sK1)) | k1_xboole_0 = sK2),
% 0.22/0.55    inference(resolution,[],[f95,f50])).
% 0.22/0.55  fof(f95,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r2_hidden(sK3(X0),X1) | k1_xboole_0 = X0) )),
% 0.22/0.55    inference(resolution,[],[f69,f64])).
% 0.22/0.55  fof(f69,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f32])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,axiom,(
% 0.22/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.22/0.55  fof(f106,plain,(
% 0.22/0.55    r2_hidden(k1_mcart_1(sK3(sK2)),k1_tarski(sK0)) | k1_xboole_0 = sK2),
% 0.22/0.55    inference(resolution,[],[f103,f72])).
% 0.22/0.55  fof(f52,plain,(
% 0.22/0.55    ~r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f42])).
% 0.22/0.55  fof(f364,plain,(
% 0.22/0.55    ( ! [X0] : (r2_hidden(k1_xboole_0,sK1) | ~r2_hidden(X0,k1_tarski(sK0))) )),
% 0.22/0.55    inference(forward_demodulation,[],[f356,f297])).
% 0.22/0.55  fof(f356,plain,(
% 0.22/0.55    ( ! [X0] : (r2_hidden(k1_funct_1(k1_xboole_0,X0),sK1) | ~r2_hidden(X0,k1_tarski(sK0))) )),
% 0.22/0.55    inference(backward_demodulation,[],[f315,f320])).
% 0.22/0.55  fof(f381,plain,(
% 0.22/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_tarski(sK0))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f373,f82])).
% 0.22/0.55  fof(f82,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.22/0.55    inference(superposition,[],[f66,f58])).
% 0.22/0.55  fof(f58,plain,(
% 0.22/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.55  fof(f66,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v1_xboole_0(k2_tarski(X0,X1))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0,X1] : ~v1_xboole_0(k2_tarski(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_xboole_0)).
% 0.22/0.55  % (29811)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  fof(f373,plain,(
% 0.22/0.55    ( ! [X0] : (v1_xboole_0(k1_tarski(sK0)) | ~m1_subset_1(X0,k1_tarski(sK0))) )),
% 0.22/0.55    inference(resolution,[],[f365,f68])).
% 0.22/0.55  fof(f68,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f31])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.55    inference(flattening,[],[f30])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,axiom,(
% 0.22/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (29808)------------------------------
% 0.22/0.55  % (29808)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (29808)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (29808)Memory used [KB]: 6524
% 0.22/0.55  % (29808)Time elapsed: 0.092 s
% 0.22/0.55  % (29808)------------------------------
% 0.22/0.55  % (29808)------------------------------
% 0.22/0.55  % (29830)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (29826)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (29817)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (29800)Success in time 0.184 s
%------------------------------------------------------------------------------
