%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:02 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 366 expanded)
%              Number of leaves         :    5 (  72 expanded)
%              Depth                    :    9
%              Number of atoms          :  192 (1763 expanded)
%              Number of equality atoms :   17 ( 111 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f127,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f25,f21,f23,f22,f26,f99,f97,f115,f117,f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_relat_1(X4)
      | ~ v1_funct_1(X4)
      | ~ r1_partfun1(X2,X4)
      | ~ r1_relset_1(X0,X1,X3,X2)
      | r1_partfun1(X3,X4) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( r1_partfun1(X3,X4)
              | ~ r1_relset_1(X0,X1,X3,X2)
              | ~ r1_partfun1(X2,X4)
              | ~ v1_funct_1(X4)
              | ~ v1_relat_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( r1_partfun1(X3,X4)
              | ~ r1_relset_1(X0,X1,X3,X2)
              | ~ r1_partfun1(X2,X4)
              | ~ v1_funct_1(X4)
              | ~ v1_relat_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( v1_funct_1(X4)
                & v1_relat_1(X4) )
             => ( ( r1_relset_1(X0,X1,X3,X2)
                  & r1_partfun1(X2,X4) )
               => r1_partfun1(X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_partfun1)).

fof(f117,plain,(
    ~ r1_partfun1(sK3,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))) ),
    inference(unit_resulting_resolution,[],[f21,f22,f97,f98,f84,f96,f48])).

fof(f48,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X5,X0)
      | ~ r1_partfun1(X2,X5)
      | r2_hidden(X5,k5_partfun1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X5,X0)
      | ~ r1_partfun1(X2,X5)
      | r2_hidden(X5,X3)
      | k5_partfun1(X0,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
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
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f3])).

% (3046)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (3054)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% (3042)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (3045)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (3055)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (3046)Refutation not found, incomplete strategy% (3046)------------------------------
% (3046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3046)Termination reason: Refutation not found, incomplete strategy

% (3046)Memory used [KB]: 10618
% (3046)Time elapsed: 0.146 s
% (3046)------------------------------
% (3046)------------------------------
% (3047)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (3043)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f3,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_partfun1)).

fof(f96,plain,(
    m1_subset_1(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f92,f91])).

fof(f91,plain,(
    sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)) = sK6(sK0,sK1,sK2,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))) ),
    inference(unit_resulting_resolution,[],[f25,f26,f83,f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK6(X0,X1,X2,X4) = X4
      | ~ r2_hidden(X4,k5_partfun1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK6(X0,X1,X2,X4) = X4
      | ~ r2_hidden(X4,X3)
      | k5_partfun1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f83,plain,(
    r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),k5_partfun1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f24,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f24,plain,(
    ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
          & r1_relset_1(X0,X1,X3,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
          & r1_relset_1(X0,X1,X3,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X3) )
           => ( r1_relset_1(X0,X1,X3,X2)
             => r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( r1_relset_1(X0,X1,X3,X2)
           => r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t165_funct_2)).

fof(f92,plain,(
    m1_subset_1(sK6(sK0,sK1,sK2,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f25,f26,f83,f52])).

% (3053)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X4,k5_partfun1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(sK6(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X4,X3)
      | k5_partfun1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f84,plain,(
    ~ r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),k5_partfun1(sK0,sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f24,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f98,plain,(
    v1_partfun1(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),sK0) ),
    inference(forward_demodulation,[],[f90,f91])).

fof(f90,plain,(
    v1_partfun1(sK6(sK0,sK1,sK2,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))),sK0) ),
    inference(unit_resulting_resolution,[],[f25,f26,f83,f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_partfun1(sK6(X0,X1,X2,X4),X0)
      | ~ r2_hidden(X4,k5_partfun1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_partfun1(sK6(X0,X1,X2,X4),X0)
      | ~ r2_hidden(X4,X3)
      | k5_partfun1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f115,plain,(
    v1_relat_1(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))) ),
    inference(unit_resulting_resolution,[],[f96,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f97,plain,(
    v1_funct_1(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))) ),
    inference(backward_demodulation,[],[f93,f91])).

fof(f93,plain,(
    v1_funct_1(sK6(sK0,sK1,sK2,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)))) ),
    inference(unit_resulting_resolution,[],[f25,f26,f83,f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(sK6(X0,X1,X2,X4))
      | ~ r2_hidden(X4,k5_partfun1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(sK6(X0,X1,X2,X4))
      | ~ r2_hidden(X4,X3)
      | k5_partfun1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f99,plain,(
    r1_partfun1(sK2,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))) ),
    inference(forward_demodulation,[],[f89,f91])).

fof(f89,plain,(
    r1_partfun1(sK2,sK6(sK0,sK1,sK2,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)))) ),
    inference(unit_resulting_resolution,[],[f25,f26,f83,f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r1_partfun1(X2,sK6(X0,X1,X2,X4))
      | ~ r2_hidden(X4,k5_partfun1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r1_partfun1(X2,sK6(X0,X1,X2,X4))
      | ~ r2_hidden(X4,X3)
      | k5_partfun1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f26,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f10])).

fof(f22,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f10])).

fof(f23,plain,(
    r1_relset_1(sK0,sK1,sK3,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f21,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f25,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:08:02 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (3030)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (3038)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (3033)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.39/0.54  % (3034)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.39/0.54  % (3035)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.39/0.54  % (3032)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.39/0.54  % (3031)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.39/0.54  % (3049)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.39/0.54  % (3050)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.39/0.54  % (3033)Refutation found. Thanks to Tanya!
% 1.39/0.54  % SZS status Theorem for theBenchmark
% 1.39/0.54  % (3051)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.39/0.55  % (3057)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.39/0.55  % (3058)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.39/0.55  % (3037)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.39/0.55  % (3048)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.39/0.55  % (3029)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.39/0.55  % (3040)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.39/0.55  % (3039)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.51/0.55  % (3041)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.51/0.55  % (3056)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.51/0.55  % SZS output start Proof for theBenchmark
% 1.51/0.55  fof(f127,plain,(
% 1.51/0.55    $false),
% 1.51/0.55    inference(unit_resulting_resolution,[],[f25,f21,f23,f22,f26,f99,f97,f115,f117,f33])).
% 1.51/0.55  fof(f33,plain,(
% 1.51/0.55    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_relat_1(X4) | ~v1_funct_1(X4) | ~r1_partfun1(X2,X4) | ~r1_relset_1(X0,X1,X3,X2) | r1_partfun1(X3,X4)) )),
% 1.51/0.55    inference(cnf_transformation,[],[f17])).
% 1.51/0.55  fof(f17,plain,(
% 1.51/0.55    ! [X0,X1,X2] : (! [X3] : (! [X4] : (r1_partfun1(X3,X4) | ~r1_relset_1(X0,X1,X3,X2) | ~r1_partfun1(X2,X4) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.51/0.55    inference(flattening,[],[f16])).
% 1.51/0.55  fof(f16,plain,(
% 1.51/0.55    ! [X0,X1,X2] : (! [X3] : (! [X4] : ((r1_partfun1(X3,X4) | (~r1_relset_1(X0,X1,X3,X2) | ~r1_partfun1(X2,X4))) | (~v1_funct_1(X4) | ~v1_relat_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.51/0.55    inference(ennf_transformation,[],[f4])).
% 1.51/0.55  fof(f4,axiom,(
% 1.51/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ((v1_funct_1(X4) & v1_relat_1(X4)) => ((r1_relset_1(X0,X1,X3,X2) & r1_partfun1(X2,X4)) => r1_partfun1(X3,X4)))))),
% 1.51/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_partfun1)).
% 1.51/0.55  fof(f117,plain,(
% 1.51/0.55    ~r1_partfun1(sK3,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)))),
% 1.51/0.55    inference(unit_resulting_resolution,[],[f21,f22,f97,f98,f84,f96,f48])).
% 1.51/0.55  fof(f48,plain,(
% 1.51/0.55    ( ! [X2,X0,X5,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X5,X0) | ~r1_partfun1(X2,X5) | r2_hidden(X5,k5_partfun1(X0,X1,X2))) )),
% 1.51/0.55    inference(equality_resolution,[],[f47])).
% 1.51/0.55  fof(f47,plain,(
% 1.51/0.55    ( ! [X2,X0,X5,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X5,X0) | ~r1_partfun1(X2,X5) | r2_hidden(X5,X3) | k5_partfun1(X0,X1,X2) != X3) )),
% 1.51/0.55    inference(equality_resolution,[],[f45])).
% 1.51/0.55  fof(f45,plain,(
% 1.51/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X4 != X5 | ~v1_partfun1(X5,X0) | ~r1_partfun1(X2,X5) | r2_hidden(X4,X3) | k5_partfun1(X0,X1,X2) != X3) )),
% 1.51/0.55    inference(cnf_transformation,[],[f19])).
% 1.51/0.55  fof(f19,plain,(
% 1.51/0.55    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.51/0.55    inference(flattening,[],[f18])).
% 1.51/0.55  fof(f18,plain,(
% 1.51/0.55    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.51/0.55    inference(ennf_transformation,[],[f3])).
% 1.51/0.55  % (3046)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.51/0.56  % (3054)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.51/0.56  % (3042)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.51/0.56  % (3045)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.51/0.56  % (3055)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.51/0.56  % (3046)Refutation not found, incomplete strategy% (3046)------------------------------
% 1.51/0.56  % (3046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.56  % (3046)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.56  
% 1.51/0.56  % (3046)Memory used [KB]: 10618
% 1.51/0.56  % (3046)Time elapsed: 0.146 s
% 1.51/0.56  % (3046)------------------------------
% 1.51/0.56  % (3046)------------------------------
% 1.51/0.56  % (3047)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.51/0.56  % (3043)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.51/0.56  fof(f3,axiom,(
% 1.51/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_partfun1)).
% 1.51/0.56  fof(f96,plain,(
% 1.51/0.56    m1_subset_1(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.51/0.56    inference(backward_demodulation,[],[f92,f91])).
% 1.51/0.56  fof(f91,plain,(
% 1.51/0.56    sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)) = sK6(sK0,sK1,sK2,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)))),
% 1.51/0.56    inference(unit_resulting_resolution,[],[f25,f26,f83,f51])).
% 1.51/0.56  fof(f51,plain,(
% 1.51/0.56    ( ! [X4,X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK6(X0,X1,X2,X4) = X4 | ~r2_hidden(X4,k5_partfun1(X0,X1,X2))) )),
% 1.51/0.56    inference(equality_resolution,[],[f42])).
% 1.51/0.56  fof(f42,plain,(
% 1.51/0.56    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK6(X0,X1,X2,X4) = X4 | ~r2_hidden(X4,X3) | k5_partfun1(X0,X1,X2) != X3) )),
% 1.51/0.56    inference(cnf_transformation,[],[f19])).
% 1.51/0.56  fof(f83,plain,(
% 1.51/0.56    r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),k5_partfun1(sK0,sK1,sK2))),
% 1.51/0.56    inference(unit_resulting_resolution,[],[f24,f28])).
% 1.51/0.56  fof(f28,plain,(
% 1.51/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f11])).
% 1.51/0.56  fof(f11,plain,(
% 1.51/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.51/0.56    inference(ennf_transformation,[],[f1])).
% 1.51/0.56  fof(f1,axiom,(
% 1.51/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.51/0.56  fof(f24,plain,(
% 1.51/0.56    ~r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))),
% 1.51/0.56    inference(cnf_transformation,[],[f10])).
% 1.51/0.56  fof(f10,plain,(
% 1.51/0.56    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)) & r1_relset_1(X0,X1,X3,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 1.51/0.56    inference(flattening,[],[f9])).
% 1.51/0.56  fof(f9,plain,(
% 1.51/0.56    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)) & r1_relset_1(X0,X1,X3,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 1.51/0.56    inference(ennf_transformation,[],[f8])).
% 1.51/0.56  fof(f8,negated_conjecture,(
% 1.51/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (r1_relset_1(X0,X1,X3,X2) => r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)))))),
% 1.51/0.56    inference(negated_conjecture,[],[f7])).
% 1.51/0.56  fof(f7,conjecture,(
% 1.51/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (r1_relset_1(X0,X1,X3,X2) => r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)))))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t165_funct_2)).
% 1.51/0.56  fof(f92,plain,(
% 1.51/0.56    m1_subset_1(sK6(sK0,sK1,sK2,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.51/0.56    inference(unit_resulting_resolution,[],[f25,f26,f83,f52])).
% 1.51/0.56  % (3053)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.51/0.56  fof(f52,plain,(
% 1.51/0.56    ( ! [X4,X2,X0,X1] : (m1_subset_1(sK6(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~r2_hidden(X4,k5_partfun1(X0,X1,X2))) )),
% 1.51/0.56    inference(equality_resolution,[],[f41])).
% 1.51/0.56  fof(f41,plain,(
% 1.51/0.56    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(sK6(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X4,X3) | k5_partfun1(X0,X1,X2) != X3) )),
% 1.51/0.56    inference(cnf_transformation,[],[f19])).
% 1.51/0.56  fof(f84,plain,(
% 1.51/0.56    ~r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),k5_partfun1(sK0,sK1,sK3))),
% 1.51/0.56    inference(unit_resulting_resolution,[],[f24,f29])).
% 1.51/0.56  fof(f29,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f11])).
% 1.51/0.56  fof(f98,plain,(
% 1.51/0.56    v1_partfun1(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)),sK0)),
% 1.51/0.56    inference(forward_demodulation,[],[f90,f91])).
% 1.51/0.56  fof(f90,plain,(
% 1.51/0.56    v1_partfun1(sK6(sK0,sK1,sK2,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))),sK0)),
% 1.51/0.56    inference(unit_resulting_resolution,[],[f25,f26,f83,f50])).
% 1.51/0.56  fof(f50,plain,(
% 1.51/0.56    ( ! [X4,X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_partfun1(sK6(X0,X1,X2,X4),X0) | ~r2_hidden(X4,k5_partfun1(X0,X1,X2))) )),
% 1.51/0.56    inference(equality_resolution,[],[f43])).
% 1.51/0.56  fof(f43,plain,(
% 1.51/0.56    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_partfun1(sK6(X0,X1,X2,X4),X0) | ~r2_hidden(X4,X3) | k5_partfun1(X0,X1,X2) != X3) )),
% 1.51/0.56    inference(cnf_transformation,[],[f19])).
% 1.51/0.56  fof(f115,plain,(
% 1.51/0.56    v1_relat_1(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)))),
% 1.51/0.56    inference(unit_resulting_resolution,[],[f96,f46])).
% 1.51/0.56  fof(f46,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.51/0.56    inference(cnf_transformation,[],[f20])).
% 1.51/0.56  fof(f20,plain,(
% 1.51/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.56    inference(ennf_transformation,[],[f2])).
% 1.51/0.56  fof(f2,axiom,(
% 1.51/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.51/0.56  fof(f97,plain,(
% 1.51/0.56    v1_funct_1(sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)))),
% 1.51/0.56    inference(backward_demodulation,[],[f93,f91])).
% 1.51/0.56  fof(f93,plain,(
% 1.51/0.56    v1_funct_1(sK6(sK0,sK1,sK2,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))))),
% 1.51/0.56    inference(unit_resulting_resolution,[],[f25,f26,f83,f53])).
% 1.51/0.56  fof(f53,plain,(
% 1.51/0.56    ( ! [X4,X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(sK6(X0,X1,X2,X4)) | ~r2_hidden(X4,k5_partfun1(X0,X1,X2))) )),
% 1.51/0.56    inference(equality_resolution,[],[f40])).
% 1.51/0.56  fof(f40,plain,(
% 1.51/0.56    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(sK6(X0,X1,X2,X4)) | ~r2_hidden(X4,X3) | k5_partfun1(X0,X1,X2) != X3) )),
% 1.51/0.56    inference(cnf_transformation,[],[f19])).
% 1.51/0.56  fof(f99,plain,(
% 1.51/0.56    r1_partfun1(sK2,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)))),
% 1.51/0.56    inference(forward_demodulation,[],[f89,f91])).
% 1.51/0.56  fof(f89,plain,(
% 1.51/0.56    r1_partfun1(sK2,sK6(sK0,sK1,sK2,sK4(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))))),
% 1.51/0.56    inference(unit_resulting_resolution,[],[f25,f26,f83,f49])).
% 1.51/0.56  fof(f49,plain,(
% 1.51/0.56    ( ! [X4,X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r1_partfun1(X2,sK6(X0,X1,X2,X4)) | ~r2_hidden(X4,k5_partfun1(X0,X1,X2))) )),
% 1.51/0.56    inference(equality_resolution,[],[f44])).
% 1.51/0.56  fof(f44,plain,(
% 1.51/0.56    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r1_partfun1(X2,sK6(X0,X1,X2,X4)) | ~r2_hidden(X4,X3) | k5_partfun1(X0,X1,X2) != X3) )),
% 1.51/0.56    inference(cnf_transformation,[],[f19])).
% 1.51/0.56  fof(f26,plain,(
% 1.51/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.51/0.56    inference(cnf_transformation,[],[f10])).
% 1.51/0.56  fof(f22,plain,(
% 1.51/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.51/0.56    inference(cnf_transformation,[],[f10])).
% 1.51/0.56  fof(f23,plain,(
% 1.51/0.56    r1_relset_1(sK0,sK1,sK3,sK2)),
% 1.51/0.56    inference(cnf_transformation,[],[f10])).
% 1.51/0.56  fof(f21,plain,(
% 1.51/0.56    v1_funct_1(sK3)),
% 1.51/0.56    inference(cnf_transformation,[],[f10])).
% 1.51/0.56  fof(f25,plain,(
% 1.51/0.56    v1_funct_1(sK2)),
% 1.51/0.56    inference(cnf_transformation,[],[f10])).
% 1.51/0.56  % SZS output end Proof for theBenchmark
% 1.51/0.56  % (3033)------------------------------
% 1.51/0.56  % (3033)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.56  % (3033)Termination reason: Refutation
% 1.51/0.56  
% 1.51/0.56  % (3033)Memory used [KB]: 6396
% 1.51/0.56  % (3033)Time elapsed: 0.130 s
% 1.51/0.56  % (3033)------------------------------
% 1.51/0.56  % (3033)------------------------------
% 1.51/0.56  % (3028)Success in time 0.2 s
%------------------------------------------------------------------------------
