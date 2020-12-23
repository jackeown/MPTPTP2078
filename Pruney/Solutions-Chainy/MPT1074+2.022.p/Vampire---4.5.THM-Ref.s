%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:08 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  111 (1309 expanded)
%              Number of leaves         :   19 ( 456 expanded)
%              Depth                    :   32
%              Number of atoms          :  400 (9248 expanded)
%              Number of equality atoms :  100 ( 704 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f502,plain,(
    $false ),
    inference(subsumption_resolution,[],[f492,f49])).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f492,plain,(
    ~ r1_tarski(k1_xboole_0,sK4(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f108,f482])).

fof(f482,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f481,f382])).

fof(f382,plain,
    ( r2_hidden(sK5(sK1,sK0,sK3),sK1)
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f379])).

fof(f379,plain,
    ( k1_xboole_0 = sK2
    | r2_hidden(sK5(sK1,sK0,sK3),sK1)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f373,f165])).

fof(f165,plain,(
    ! [X1] :
      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | r2_hidden(sK5(sK1,X1,sK3),sK1)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f164,f94])).

fof(f94,plain,(
    v1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f53,f46,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

% (7401)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)
    & ! [X4] :
        ( r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0)
        | ~ m1_subset_1(X4,sK1) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK2)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f32,f31,f30])).

fof(f30,plain,
    ( ? [X0,X1] :
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
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(sK1,X2,X3),sK0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(sK1,X2,X3,X4),sK0)
                  | ~ m1_subset_1(X4,sK1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
              & v1_funct_2(X3,sK1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k2_relset_1(sK1,X2,X3),sK0)
            & ! [X4] :
                ( r2_hidden(k3_funct_2(sK1,X2,X3,X4),sK0)
                | ~ m1_subset_1(X4,sK1) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
            & v1_funct_2(X3,sK1,X2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k2_relset_1(sK1,sK2,X3),sK0)
          & ! [X4] :
              ( r2_hidden(k3_funct_2(sK1,sK2,X3,X4),sK0)
              | ~ m1_subset_1(X4,sK1) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X3,sK1,sK2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,X3),sK0)
        & ! [X4] :
            ( r2_hidden(k3_funct_2(sK1,sK2,X3,X4),sK0)
            | ~ m1_subset_1(X4,sK1) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        & v1_funct_2(X3,sK1,sK2)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)
      & ! [X4] :
          ( r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0)
          | ~ m1_subset_1(X4,sK1) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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

fof(f53,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f164,plain,(
    ! [X1] :
      ( r2_hidden(sK5(sK1,X1,sK3),sK1)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | ~ v1_relat_1(sK3)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f161,f44])).

fof(f44,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f161,plain,(
    ! [X1] :
      ( r2_hidden(sK5(sK1,X1,sK3),sK1)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3)
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f80,f137])).

fof(f137,plain,
    ( sK1 = k1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f102,f92])).

fof(f92,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f46,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f102,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f95,f45])).

fof(f45,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f95,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3) ),
    inference(resolution,[],[f46,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f39])).

% (7400)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f39,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f80,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK5(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK5(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ( ~ r2_hidden(k1_funct_1(X2,sK5(X0,X1,X2)),X1)
        & r2_hidden(sK5(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK5(X0,X1,X2)),X1)
        & r2_hidden(sK5(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

fof(f373,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f372,f104])).

fof(f104,plain,(
    ~ m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f100,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f100,plain,(
    ~ r1_tarski(k2_relat_1(sK3),sK0) ),
    inference(backward_demodulation,[],[f48,f91])).

fof(f91,plain,(
    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f46,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f48,plain,(
    ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f372,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f60,f371])).

fof(f371,plain,
    ( k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f370,f213])).

% (7397)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f213,plain,(
    ! [X4] :
      ( r2_hidden(sK5(sK1,X4,sK3),sK1)
      | k1_xboole_0 = sK2
      | k2_relat_1(sK3) = k2_relset_1(sK1,X4,sK3) ) ),
    inference(resolution,[],[f165,f59])).

fof(f370,plain,
    ( k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3)
    | k1_xboole_0 = sK2
    | ~ r2_hidden(sK5(sK1,sK0,sK3),sK1) ),
    inference(resolution,[],[f369,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f369,plain,
    ( ~ m1_subset_1(sK5(sK1,sK0,sK3),sK1)
    | k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f368,f59])).

fof(f368,plain,
    ( ~ m1_subset_1(sK5(sK1,sK0,sK3),sK1)
    | k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3)
    | k1_xboole_0 = sK2
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(duplicate_literal_removal,[],[f365])).

fof(f365,plain,
    ( ~ m1_subset_1(sK5(sK1,sK0,sK3),sK1)
    | k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3)
    | k1_xboole_0 = sK2
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f329,f177])).

fof(f177,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_funct_1(sK3,sK5(sK1,X0,sK3)),X0)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f145,f137])).

fof(f145,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_funct_1(sK3,sK5(k1_relat_1(sK3),X0,sK3)),X0)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) ) ),
    inference(resolution,[],[f89,f94])).

fof(f89,plain,(
    ! [X4] :
      ( ~ v1_relat_1(sK3)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X4)))
      | ~ r2_hidden(k1_funct_1(sK3,sK5(k1_relat_1(sK3),X4,sK3)),X4) ) ),
    inference(resolution,[],[f44,f79])).

fof(f79,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k1_funct_1(X2,sK5(k1_relat_1(X2),X1,X2)),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK5(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f329,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK3,sK5(sK1,X0,sK3)),sK0)
      | ~ m1_subset_1(sK5(sK1,X0,sK3),sK1)
      | k2_relat_1(sK3) = k2_relset_1(sK1,X0,sK3)
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f47,f248])).

fof(f248,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,sK5(sK1,X0,sK3)) = k3_funct_2(sK1,sK2,sK3,sK5(sK1,X0,sK3))
      | k2_relat_1(sK3) = k2_relset_1(sK1,X0,sK3)
      | k1_xboole_0 = sK2 ) ),
    inference(resolution,[],[f213,f168])).

fof(f168,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0) ) ),
    inference(resolution,[],[f155,f54])).

fof(f155,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f154,f42])).

fof(f42,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f154,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0)
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f151,f45])).

fof(f151,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | ~ v1_funct_2(sK3,sK1,sK2)
      | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0)
      | v1_xboole_0(sK1) ) ),
    inference(resolution,[],[f87,f46])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ m1_subset_1(X0,X1)
      | ~ v1_funct_2(sK3,X1,X2)
      | k3_funct_2(X1,X2,sK3,X0) = k1_funct_1(sK3,X0)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f44,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f47,plain,(
    ! [X4] :
      ( r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0)
      | ~ m1_subset_1(X4,sK1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

% (7403)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f481,plain,
    ( k1_xboole_0 = sK2
    | ~ r2_hidden(sK5(sK1,sK0,sK3),sK1) ),
    inference(resolution,[],[f477,f54])).

fof(f477,plain,
    ( ~ m1_subset_1(sK5(sK1,sK0,sK3),sK1)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f476,f373])).

fof(f476,plain,
    ( ~ m1_subset_1(sK5(sK1,sK0,sK3),sK1)
    | k1_xboole_0 = sK2
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(duplicate_literal_removal,[],[f473])).

fof(f473,plain,
    ( ~ m1_subset_1(sK5(sK1,sK0,sK3),sK1)
    | k1_xboole_0 = sK2
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f472,f177])).

fof(f472,plain,
    ( r2_hidden(k1_funct_1(sK3,sK5(sK1,sK0,sK3)),sK0)
    | ~ m1_subset_1(sK5(sK1,sK0,sK3),sK1)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f47,f384])).

fof(f384,plain,
    ( k1_funct_1(sK3,sK5(sK1,sK0,sK3)) = k3_funct_2(sK1,sK2,sK3,sK5(sK1,sK0,sK3))
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f383])).

fof(f383,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK2
    | k1_funct_1(sK3,sK5(sK1,sK0,sK3)) = k3_funct_2(sK1,sK2,sK3,sK5(sK1,sK0,sK3)) ),
    inference(resolution,[],[f380,f240])).

fof(f240,plain,(
    ! [X0] :
      ( r1_tarski(sK3,k2_zfmisc_1(sK1,X0))
      | k1_xboole_0 = sK2
      | k1_funct_1(sK3,sK5(sK1,X0,sK3)) = k3_funct_2(sK1,sK2,sK3,sK5(sK1,X0,sK3)) ) ),
    inference(resolution,[],[f217,f168])).

fof(f217,plain,(
    ! [X6] :
      ( r2_hidden(sK5(sK1,X6,sK3),sK1)
      | k1_xboole_0 = sK2
      | r1_tarski(sK3,k2_zfmisc_1(sK1,X6)) ) ),
    inference(resolution,[],[f165,f55])).

fof(f380,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(sK1,sK0))
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f373,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f108,plain,(
    ~ r1_tarski(sK2,sK4(sK2)) ),
    inference(unit_resulting_resolution,[],[f86,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f86,plain,(
    r2_hidden(sK4(sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f43,f52])).

fof(f52,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f43,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:14:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (7411)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (7402)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (7412)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.51  % (7404)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.53  % (7416)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.54  % (7407)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.54  % (7410)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.55  % (7399)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 1.51/0.56  % (7412)Refutation found. Thanks to Tanya!
% 1.51/0.56  % SZS status Theorem for theBenchmark
% 1.51/0.56  % SZS output start Proof for theBenchmark
% 1.51/0.56  fof(f502,plain,(
% 1.51/0.56    $false),
% 1.51/0.56    inference(subsumption_resolution,[],[f492,f49])).
% 1.51/0.56  fof(f49,plain,(
% 1.51/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f2])).
% 1.51/0.56  fof(f2,axiom,(
% 1.51/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.51/0.56  fof(f492,plain,(
% 1.51/0.56    ~r1_tarski(k1_xboole_0,sK4(k1_xboole_0))),
% 1.51/0.56    inference(backward_demodulation,[],[f108,f482])).
% 1.51/0.56  fof(f482,plain,(
% 1.51/0.56    k1_xboole_0 = sK2),
% 1.51/0.56    inference(subsumption_resolution,[],[f481,f382])).
% 1.51/0.56  fof(f382,plain,(
% 1.51/0.56    r2_hidden(sK5(sK1,sK0,sK3),sK1) | k1_xboole_0 = sK2),
% 1.51/0.56    inference(duplicate_literal_removal,[],[f379])).
% 1.51/0.56  fof(f379,plain,(
% 1.51/0.56    k1_xboole_0 = sK2 | r2_hidden(sK5(sK1,sK0,sK3),sK1) | k1_xboole_0 = sK2),
% 1.51/0.56    inference(resolution,[],[f373,f165])).
% 1.51/0.56  fof(f165,plain,(
% 1.51/0.56    ( ! [X1] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | r2_hidden(sK5(sK1,X1,sK3),sK1) | k1_xboole_0 = sK2) )),
% 1.51/0.56    inference(subsumption_resolution,[],[f164,f94])).
% 1.51/0.56  fof(f94,plain,(
% 1.51/0.56    v1_relat_1(sK3)),
% 1.51/0.56    inference(unit_resulting_resolution,[],[f53,f46,f50])).
% 1.51/0.56  fof(f50,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f18])).
% 1.51/0.56  fof(f18,plain,(
% 1.51/0.56    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.51/0.56    inference(ennf_transformation,[],[f5])).
% 1.51/0.56  % (7401)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 1.51/0.56  fof(f5,axiom,(
% 1.51/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.51/0.56  fof(f46,plain,(
% 1.51/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.51/0.56    inference(cnf_transformation,[],[f33])).
% 1.51/0.56  fof(f33,plain,(
% 1.51/0.56    ((~r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)),
% 1.51/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f32,f31,f30])).
% 1.51/0.56  fof(f30,plain,(
% 1.51/0.56    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK1,X2,X3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,X2,X3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) & v1_funct_2(X3,sK1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))),
% 1.51/0.56    introduced(choice_axiom,[])).
% 1.51/0.56  fof(f31,plain,(
% 1.51/0.56    ? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK1,X2,X3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,X2,X3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) & v1_funct_2(X3,sK1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (~r1_tarski(k2_relset_1(sK1,sK2,X3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,sK2,X3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & ~v1_xboole_0(sK2))),
% 1.51/0.56    introduced(choice_axiom,[])).
% 1.51/0.56  fof(f32,plain,(
% 1.51/0.56    ? [X3] : (~r1_tarski(k2_relset_1(sK1,sK2,X3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,sK2,X3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) => (~r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 1.51/0.56    introduced(choice_axiom,[])).
% 1.51/0.56  fof(f17,plain,(
% 1.51/0.56    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 1.51/0.56    inference(flattening,[],[f16])).
% 1.51/0.56  fof(f16,plain,(
% 1.51/0.56    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 1.51/0.56    inference(ennf_transformation,[],[f15])).
% 1.51/0.56  fof(f15,negated_conjecture,(
% 1.51/0.56    ~! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 1.51/0.56    inference(negated_conjecture,[],[f14])).
% 1.51/0.56  fof(f14,conjecture,(
% 1.51/0.56    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_funct_2)).
% 1.51/0.56  fof(f53,plain,(
% 1.51/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.51/0.56    inference(cnf_transformation,[],[f6])).
% 1.51/0.56  fof(f6,axiom,(
% 1.51/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.51/0.56  fof(f164,plain,(
% 1.51/0.56    ( ! [X1] : (r2_hidden(sK5(sK1,X1,sK3),sK1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_relat_1(sK3) | k1_xboole_0 = sK2) )),
% 1.51/0.56    inference(subsumption_resolution,[],[f161,f44])).
% 1.51/0.56  fof(f44,plain,(
% 1.51/0.56    v1_funct_1(sK3)),
% 1.51/0.56    inference(cnf_transformation,[],[f33])).
% 1.51/0.56  fof(f161,plain,(
% 1.51/0.56    ( ! [X1] : (r2_hidden(sK5(sK1,X1,sK3),sK1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | k1_xboole_0 = sK2) )),
% 1.51/0.56    inference(superposition,[],[f80,f137])).
% 1.51/0.56  fof(f137,plain,(
% 1.51/0.56    sK1 = k1_relat_1(sK3) | k1_xboole_0 = sK2),
% 1.51/0.56    inference(superposition,[],[f102,f92])).
% 1.51/0.56  fof(f92,plain,(
% 1.51/0.56    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3)),
% 1.51/0.56    inference(unit_resulting_resolution,[],[f46,f58])).
% 1.51/0.56  fof(f58,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f21])).
% 1.51/0.56  fof(f21,plain,(
% 1.51/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.56    inference(ennf_transformation,[],[f9])).
% 1.51/0.56  fof(f9,axiom,(
% 1.51/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.51/0.56  fof(f102,plain,(
% 1.51/0.56    sK1 = k1_relset_1(sK1,sK2,sK3) | k1_xboole_0 = sK2),
% 1.51/0.56    inference(subsumption_resolution,[],[f95,f45])).
% 1.51/0.56  fof(f45,plain,(
% 1.51/0.56    v1_funct_2(sK3,sK1,sK2)),
% 1.51/0.56    inference(cnf_transformation,[],[f33])).
% 1.51/0.56  fof(f95,plain,(
% 1.51/0.56    ~v1_funct_2(sK3,sK1,sK2) | k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3)),
% 1.51/0.56    inference(resolution,[],[f46,f61])).
% 1.51/0.56  fof(f61,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.51/0.56    inference(cnf_transformation,[],[f39])).
% 1.51/0.56  % (7400)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 1.51/0.56  fof(f39,plain,(
% 1.51/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.56    inference(nnf_transformation,[],[f25])).
% 1.51/0.56  fof(f25,plain,(
% 1.51/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.56    inference(flattening,[],[f24])).
% 1.51/0.56  fof(f24,plain,(
% 1.51/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.56    inference(ennf_transformation,[],[f11])).
% 1.51/0.56  fof(f11,axiom,(
% 1.51/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.51/0.56  fof(f80,plain,(
% 1.51/0.56    ( ! [X2,X1] : (r2_hidden(sK5(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.51/0.56    inference(equality_resolution,[],[f71])).
% 1.51/0.56  fof(f71,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK5(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f41])).
% 1.51/0.56  fof(f41,plain,(
% 1.51/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~r2_hidden(k1_funct_1(X2,sK5(X0,X1,X2)),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.51/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f40])).
% 1.51/0.56  fof(f40,plain,(
% 1.51/0.56    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK5(X0,X1,X2)),X1) & r2_hidden(sK5(X0,X1,X2),X0)))),
% 1.51/0.56    introduced(choice_axiom,[])).
% 1.51/0.56  fof(f27,plain,(
% 1.51/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.51/0.56    inference(flattening,[],[f26])).
% 1.51/0.56  fof(f26,plain,(
% 1.51/0.56    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.51/0.56    inference(ennf_transformation,[],[f13])).
% 1.51/0.56  fof(f13,axiom,(
% 1.51/0.56    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).
% 1.51/0.56  fof(f373,plain,(
% 1.51/0.56    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK2),
% 1.51/0.56    inference(subsumption_resolution,[],[f372,f104])).
% 1.51/0.56  fof(f104,plain,(
% 1.51/0.56    ~m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK0))),
% 1.51/0.56    inference(unit_resulting_resolution,[],[f100,f55])).
% 1.51/0.56  fof(f55,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f38])).
% 1.51/0.56  fof(f38,plain,(
% 1.51/0.56    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.51/0.56    inference(nnf_transformation,[],[f4])).
% 1.51/0.56  fof(f4,axiom,(
% 1.51/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.51/0.56  fof(f100,plain,(
% 1.51/0.56    ~r1_tarski(k2_relat_1(sK3),sK0)),
% 1.51/0.56    inference(backward_demodulation,[],[f48,f91])).
% 1.51/0.56  fof(f91,plain,(
% 1.51/0.56    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)),
% 1.51/0.56    inference(unit_resulting_resolution,[],[f46,f59])).
% 1.51/0.56  fof(f59,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f22])).
% 1.51/0.56  fof(f22,plain,(
% 1.51/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.56    inference(ennf_transformation,[],[f10])).
% 1.51/0.56  fof(f10,axiom,(
% 1.51/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.51/0.56  fof(f48,plain,(
% 1.51/0.56    ~r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)),
% 1.51/0.56    inference(cnf_transformation,[],[f33])).
% 1.51/0.56  fof(f372,plain,(
% 1.51/0.56    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK2),
% 1.51/0.56    inference(superposition,[],[f60,f371])).
% 1.51/0.56  fof(f371,plain,(
% 1.51/0.56    k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3) | k1_xboole_0 = sK2),
% 1.51/0.56    inference(subsumption_resolution,[],[f370,f213])).
% 1.51/0.56  % (7397)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 1.51/0.56  fof(f213,plain,(
% 1.51/0.56    ( ! [X4] : (r2_hidden(sK5(sK1,X4,sK3),sK1) | k1_xboole_0 = sK2 | k2_relat_1(sK3) = k2_relset_1(sK1,X4,sK3)) )),
% 1.51/0.56    inference(resolution,[],[f165,f59])).
% 1.51/0.56  fof(f370,plain,(
% 1.51/0.56    k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3) | k1_xboole_0 = sK2 | ~r2_hidden(sK5(sK1,sK0,sK3),sK1)),
% 1.51/0.56    inference(resolution,[],[f369,f54])).
% 1.51/0.56  fof(f54,plain,(
% 1.51/0.56    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f19])).
% 1.51/0.56  fof(f19,plain,(
% 1.51/0.56    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.51/0.56    inference(ennf_transformation,[],[f3])).
% 1.51/0.56  fof(f3,axiom,(
% 1.51/0.56    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.51/0.56  fof(f369,plain,(
% 1.51/0.56    ~m1_subset_1(sK5(sK1,sK0,sK3),sK1) | k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3) | k1_xboole_0 = sK2),
% 1.51/0.56    inference(subsumption_resolution,[],[f368,f59])).
% 1.51/0.56  fof(f368,plain,(
% 1.51/0.56    ~m1_subset_1(sK5(sK1,sK0,sK3),sK1) | k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3) | k1_xboole_0 = sK2 | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.51/0.56    inference(duplicate_literal_removal,[],[f365])).
% 1.51/0.56  fof(f365,plain,(
% 1.51/0.56    ~m1_subset_1(sK5(sK1,sK0,sK3),sK1) | k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3) | k1_xboole_0 = sK2 | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK2),
% 1.51/0.56    inference(resolution,[],[f329,f177])).
% 1.51/0.56  fof(f177,plain,(
% 1.51/0.56    ( ! [X0] : (~r2_hidden(k1_funct_1(sK3,sK5(sK1,X0,sK3)),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | k1_xboole_0 = sK2) )),
% 1.51/0.56    inference(superposition,[],[f145,f137])).
% 1.51/0.56  fof(f145,plain,(
% 1.51/0.56    ( ! [X0] : (~r2_hidden(k1_funct_1(sK3,sK5(k1_relat_1(sK3),X0,sK3)),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))) )),
% 1.51/0.56    inference(resolution,[],[f89,f94])).
% 1.51/0.56  fof(f89,plain,(
% 1.51/0.56    ( ! [X4] : (~v1_relat_1(sK3) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X4))) | ~r2_hidden(k1_funct_1(sK3,sK5(k1_relat_1(sK3),X4,sK3)),X4)) )),
% 1.51/0.56    inference(resolution,[],[f44,f79])).
% 1.51/0.56  fof(f79,plain,(
% 1.51/0.56    ( ! [X2,X1] : (~v1_funct_1(X2) | ~r2_hidden(k1_funct_1(X2,sK5(k1_relat_1(X2),X1,X2)),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | ~v1_relat_1(X2)) )),
% 1.51/0.56    inference(equality_resolution,[],[f72])).
% 1.51/0.56  fof(f72,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(k1_funct_1(X2,sK5(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f41])).
% 1.51/0.56  fof(f329,plain,(
% 1.51/0.56    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,sK5(sK1,X0,sK3)),sK0) | ~m1_subset_1(sK5(sK1,X0,sK3),sK1) | k2_relat_1(sK3) = k2_relset_1(sK1,X0,sK3) | k1_xboole_0 = sK2) )),
% 1.51/0.56    inference(superposition,[],[f47,f248])).
% 1.51/0.56  fof(f248,plain,(
% 1.51/0.56    ( ! [X0] : (k1_funct_1(sK3,sK5(sK1,X0,sK3)) = k3_funct_2(sK1,sK2,sK3,sK5(sK1,X0,sK3)) | k2_relat_1(sK3) = k2_relset_1(sK1,X0,sK3) | k1_xboole_0 = sK2) )),
% 1.51/0.56    inference(resolution,[],[f213,f168])).
% 1.51/0.56  fof(f168,plain,(
% 1.51/0.56    ( ! [X0] : (~r2_hidden(X0,sK1) | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0)) )),
% 1.51/0.56    inference(resolution,[],[f155,f54])).
% 1.51/0.56  fof(f155,plain,(
% 1.51/0.56    ( ! [X0] : (~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0)) )),
% 1.51/0.56    inference(subsumption_resolution,[],[f154,f42])).
% 1.51/0.56  fof(f42,plain,(
% 1.51/0.56    ~v1_xboole_0(sK1)),
% 1.51/0.56    inference(cnf_transformation,[],[f33])).
% 1.51/0.56  fof(f154,plain,(
% 1.51/0.56    ( ! [X0] : (~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0) | v1_xboole_0(sK1)) )),
% 1.51/0.56    inference(subsumption_resolution,[],[f151,f45])).
% 1.51/0.56  fof(f151,plain,(
% 1.51/0.56    ( ! [X0] : (~m1_subset_1(X0,sK1) | ~v1_funct_2(sK3,sK1,sK2) | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0) | v1_xboole_0(sK1)) )),
% 1.51/0.56    inference(resolution,[],[f87,f46])).
% 1.51/0.56  fof(f87,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X0,X1) | ~v1_funct_2(sK3,X1,X2) | k3_funct_2(X1,X2,sK3,X0) = k1_funct_1(sK3,X0) | v1_xboole_0(X1)) )),
% 1.51/0.56    inference(resolution,[],[f44,f73])).
% 1.51/0.56  fof(f73,plain,(
% 1.51/0.56    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | v1_xboole_0(X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f29])).
% 1.51/0.56  fof(f29,plain,(
% 1.51/0.56    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 1.51/0.56    inference(flattening,[],[f28])).
% 1.51/0.56  fof(f28,plain,(
% 1.51/0.56    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 1.51/0.56    inference(ennf_transformation,[],[f12])).
% 1.51/0.56  fof(f12,axiom,(
% 1.51/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 1.51/0.56  fof(f47,plain,(
% 1.51/0.56    ( ! [X4] : (r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0) | ~m1_subset_1(X4,sK1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f33])).
% 1.51/0.56  fof(f60,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.51/0.56    inference(cnf_transformation,[],[f23])).
% 1.51/0.56  fof(f23,plain,(
% 1.51/0.56    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.56    inference(ennf_transformation,[],[f8])).
% 1.51/0.56  fof(f8,axiom,(
% 1.51/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 1.51/0.56  % (7403)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 1.51/0.56  fof(f481,plain,(
% 1.51/0.56    k1_xboole_0 = sK2 | ~r2_hidden(sK5(sK1,sK0,sK3),sK1)),
% 1.51/0.56    inference(resolution,[],[f477,f54])).
% 1.51/0.56  fof(f477,plain,(
% 1.51/0.56    ~m1_subset_1(sK5(sK1,sK0,sK3),sK1) | k1_xboole_0 = sK2),
% 1.51/0.56    inference(subsumption_resolution,[],[f476,f373])).
% 1.51/0.56  fof(f476,plain,(
% 1.51/0.56    ~m1_subset_1(sK5(sK1,sK0,sK3),sK1) | k1_xboole_0 = sK2 | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.51/0.56    inference(duplicate_literal_removal,[],[f473])).
% 1.51/0.56  fof(f473,plain,(
% 1.51/0.56    ~m1_subset_1(sK5(sK1,sK0,sK3),sK1) | k1_xboole_0 = sK2 | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK2),
% 1.51/0.56    inference(resolution,[],[f472,f177])).
% 1.51/0.56  fof(f472,plain,(
% 1.51/0.56    r2_hidden(k1_funct_1(sK3,sK5(sK1,sK0,sK3)),sK0) | ~m1_subset_1(sK5(sK1,sK0,sK3),sK1) | k1_xboole_0 = sK2),
% 1.51/0.56    inference(superposition,[],[f47,f384])).
% 1.51/0.56  fof(f384,plain,(
% 1.51/0.56    k1_funct_1(sK3,sK5(sK1,sK0,sK3)) = k3_funct_2(sK1,sK2,sK3,sK5(sK1,sK0,sK3)) | k1_xboole_0 = sK2),
% 1.51/0.56    inference(duplicate_literal_removal,[],[f383])).
% 1.51/0.56  fof(f383,plain,(
% 1.51/0.56    k1_xboole_0 = sK2 | k1_xboole_0 = sK2 | k1_funct_1(sK3,sK5(sK1,sK0,sK3)) = k3_funct_2(sK1,sK2,sK3,sK5(sK1,sK0,sK3))),
% 1.51/0.56    inference(resolution,[],[f380,f240])).
% 1.51/0.56  fof(f240,plain,(
% 1.51/0.56    ( ! [X0] : (r1_tarski(sK3,k2_zfmisc_1(sK1,X0)) | k1_xboole_0 = sK2 | k1_funct_1(sK3,sK5(sK1,X0,sK3)) = k3_funct_2(sK1,sK2,sK3,sK5(sK1,X0,sK3))) )),
% 1.51/0.56    inference(resolution,[],[f217,f168])).
% 1.51/0.56  fof(f217,plain,(
% 1.51/0.56    ( ! [X6] : (r2_hidden(sK5(sK1,X6,sK3),sK1) | k1_xboole_0 = sK2 | r1_tarski(sK3,k2_zfmisc_1(sK1,X6))) )),
% 1.51/0.56    inference(resolution,[],[f165,f55])).
% 1.51/0.56  fof(f380,plain,(
% 1.51/0.56    ~r1_tarski(sK3,k2_zfmisc_1(sK1,sK0)) | k1_xboole_0 = sK2),
% 1.51/0.56    inference(resolution,[],[f373,f56])).
% 1.51/0.56  fof(f56,plain,(
% 1.51/0.56    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f38])).
% 1.51/0.56  fof(f108,plain,(
% 1.51/0.56    ~r1_tarski(sK2,sK4(sK2))),
% 1.51/0.56    inference(unit_resulting_resolution,[],[f86,f57])).
% 1.51/0.56  fof(f57,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f20])).
% 1.51/0.56  fof(f20,plain,(
% 1.51/0.56    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.51/0.56    inference(ennf_transformation,[],[f7])).
% 1.51/0.56  fof(f7,axiom,(
% 1.51/0.56    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.51/0.56  fof(f86,plain,(
% 1.51/0.56    r2_hidden(sK4(sK2),sK2)),
% 1.51/0.56    inference(unit_resulting_resolution,[],[f43,f52])).
% 1.51/0.56  fof(f52,plain,(
% 1.51/0.56    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f37])).
% 1.51/0.56  fof(f37,plain,(
% 1.51/0.56    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.51/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).
% 1.51/0.56  fof(f36,plain,(
% 1.51/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 1.51/0.56    introduced(choice_axiom,[])).
% 1.51/0.56  fof(f35,plain,(
% 1.51/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.51/0.56    inference(rectify,[],[f34])).
% 1.51/0.56  fof(f34,plain,(
% 1.51/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.51/0.56    inference(nnf_transformation,[],[f1])).
% 1.51/0.56  fof(f1,axiom,(
% 1.51/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.51/0.56  fof(f43,plain,(
% 1.51/0.56    ~v1_xboole_0(sK2)),
% 1.51/0.56    inference(cnf_transformation,[],[f33])).
% 1.51/0.56  % SZS output end Proof for theBenchmark
% 1.51/0.56  % (7412)------------------------------
% 1.51/0.56  % (7412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.56  % (7412)Termination reason: Refutation
% 1.51/0.56  
% 1.51/0.56  % (7412)Memory used [KB]: 6908
% 1.51/0.56  % (7412)Time elapsed: 0.061 s
% 1.51/0.56  % (7412)------------------------------
% 1.51/0.56  % (7412)------------------------------
% 1.51/0.57  % (7396)Success in time 0.205 s
%------------------------------------------------------------------------------
