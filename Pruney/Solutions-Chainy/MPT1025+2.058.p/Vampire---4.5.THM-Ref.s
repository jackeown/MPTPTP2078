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
% DateTime   : Thu Dec  3 13:06:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 150 expanded)
%              Number of leaves         :    8 (  48 expanded)
%              Depth                    :   15
%              Number of atoms          :  208 ( 968 expanded)
%              Number of equality atoms :   19 ( 139 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f111,plain,(
    $false ),
    inference(subsumption_resolution,[],[f110,f22])).

fof(f22,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ! [X5] :
        ( k1_funct_1(sK3,X5) != sK4
        | ~ r2_hidden(X5,sK2)
        | ~ m1_subset_1(X5,sK0) )
    & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f7,f12,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK3,X5) != X4
              | ~ r2_hidden(X5,sK2)
              | ~ m1_subset_1(X5,sK0) )
          & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X4] :
        ( ! [X5] :
            ( k1_funct_1(sK3,X5) != X4
            | ~ r2_hidden(X5,sK2)
            | ~ m1_subset_1(X5,sK0) )
        & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) )
   => ( ! [X5] :
          ( k1_funct_1(sK3,X5) != sK4
          | ~ r2_hidden(X5,sK2)
          | ~ m1_subset_1(X5,sK0) )
      & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2) ) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

fof(f110,plain,(
    ~ v1_funct_2(sK3,sK0,sK1) ),
    inference(subsumption_resolution,[],[f109,f23])).

fof(f23,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f109,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK3,sK0,sK1) ),
    inference(resolution,[],[f91,f24])).

fof(f24,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f91,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4,k7_relset_1(sK0,X0,sK3,sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | ~ v1_funct_2(sK3,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f89,f64])).

fof(f64,plain,(
    r2_hidden(sK6(sK0,sK2,sK3,sK4),sK2) ),
    inference(subsumption_resolution,[],[f63,f21])).

fof(f21,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f63,plain,
    ( r2_hidden(sK6(sK0,sK2,sK3,sK4),sK2)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f62,f22])).

fof(f62,plain,
    ( r2_hidden(sK6(sK0,sK2,sK3,sK4),sK2)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f60,f23])).

fof(f60,plain,
    ( r2_hidden(sK6(sK0,sK2,sK3,sK4),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f33,f24])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
      | r2_hidden(sK6(X0,X2,X3,X4),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( k1_funct_1(X3,sK6(X0,X2,X3,X4)) = X4
            & r2_hidden(sK6(X0,X2,X3,X4),X2)
            & r2_hidden(sK6(X0,X2,X3,X4),X0) )
          | ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f10,f19])).

fof(f19,plain,(
    ! [X4,X3,X2,X0] :
      ( ? [X5] :
          ( k1_funct_1(X3,X5) = X4
          & r2_hidden(X5,X2)
          & r2_hidden(X5,X0) )
     => ( k1_funct_1(X3,sK6(X0,X2,X3,X4)) = X4
        & r2_hidden(sK6(X0,X2,X3,X4),X2)
        & r2_hidden(sK6(X0,X2,X3,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ? [X5] :
              ( k1_funct_1(X3,X5) = X4
              & r2_hidden(X5,X2)
              & r2_hidden(X5,X0) )
          | ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ? [X5] :
              ( k1_funct_1(X3,X5) = X4
              & r2_hidden(X5,X2)
              & r2_hidden(X5,X0) )
          | ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ~ ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).

fof(f89,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK6(sK0,sK2,sK3,sK4),sK2)
      | ~ r2_hidden(sK4,k7_relset_1(sK0,X0,sK3,sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | ~ v1_funct_2(sK3,sK0,X0) ) ),
    inference(resolution,[],[f76,f69])).

fof(f69,plain,(
    m1_subset_1(sK6(sK0,sK2,sK3,sK4),sK0) ),
    inference(resolution,[],[f59,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f29,f26])).

fof(f26,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK5(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f15,f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f59,plain,(
    r2_hidden(sK6(sK0,sK2,sK3,sK4),sK0) ),
    inference(subsumption_resolution,[],[f58,f21])).

fof(f58,plain,
    ( r2_hidden(sK6(sK0,sK2,sK3,sK4),sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f57,f22])).

fof(f57,plain,
    ( r2_hidden(sK6(sK0,sK2,sK3,sK4),sK0)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f55,f23])).

fof(f55,plain,
    ( r2_hidden(sK6(sK0,sK2,sK3,sK4),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f32,f24])).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
      | r2_hidden(sK6(X0,X2,X3,X4),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK6(X0,X1,sK3,sK4),sK0)
      | ~ r2_hidden(sK6(X0,X1,sK3,sK4),sK2)
      | ~ r2_hidden(sK4,k7_relset_1(X0,X2,sK3,X1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ v1_funct_2(sK3,X0,X2) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( sK4 != X2
      | ~ r2_hidden(sK6(X0,X1,sK3,X2),sK2)
      | ~ m1_subset_1(sK6(X0,X1,sK3,X2),sK0)
      | ~ r2_hidden(X2,k7_relset_1(X0,X3,sK3,X1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ v1_funct_2(sK3,X0,X3) ) ),
    inference(subsumption_resolution,[],[f67,f21])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( sK4 != X2
      | ~ r2_hidden(sK6(X0,X1,sK3,X2),sK2)
      | ~ m1_subset_1(sK6(X0,X1,sK3,X2),sK0)
      | ~ r2_hidden(X2,k7_relset_1(X0,X3,sK3,X1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ v1_funct_2(sK3,X0,X3)
      | ~ v1_funct_1(sK3) ) ),
    inference(superposition,[],[f25,f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_funct_1(X3,sK6(X0,X2,X3,X4)) = X4
      | ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f25,plain,(
    ! [X5] :
      ( k1_funct_1(sK3,X5) != sK4
      | ~ r2_hidden(X5,sK2)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:01:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.36  ipcrm: permission denied for id (721256449)
% 0.14/0.36  ipcrm: permission denied for id (721289218)
% 0.14/0.37  ipcrm: permission denied for id (721321989)
% 0.14/0.37  ipcrm: permission denied for id (721354758)
% 0.14/0.37  ipcrm: permission denied for id (721387527)
% 0.14/0.37  ipcrm: permission denied for id (721420297)
% 0.14/0.39  ipcrm: permission denied for id (721518623)
% 0.14/0.39  ipcrm: permission denied for id (721551392)
% 0.14/0.40  ipcrm: permission denied for id (721584161)
% 0.14/0.40  ipcrm: permission denied for id (721616931)
% 0.14/0.40  ipcrm: permission denied for id (721682470)
% 0.21/0.42  ipcrm: permission denied for id (721846326)
% 0.21/0.46  ipcrm: permission denied for id (722141282)
% 0.21/0.46  ipcrm: permission denied for id (722174051)
% 0.21/0.47  ipcrm: permission denied for id (722206821)
% 0.21/0.47  ipcrm: permission denied for id (722272363)
% 0.21/0.48  ipcrm: permission denied for id (722337903)
% 0.21/0.48  ipcrm: permission denied for id (722370673)
% 0.21/0.49  ipcrm: permission denied for id (722436215)
% 0.21/0.59  % (19485)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.59  % (19500)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.59  % (19484)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.60  % (19485)Refutation not found, incomplete strategy% (19485)------------------------------
% 0.21/0.60  % (19485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (19485)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.60  
% 0.21/0.60  % (19485)Memory used [KB]: 10746
% 0.21/0.60  % (19485)Time elapsed: 0.064 s
% 0.21/0.60  % (19485)------------------------------
% 0.21/0.60  % (19485)------------------------------
% 0.21/0.60  % (19484)Refutation found. Thanks to Tanya!
% 0.21/0.60  % SZS status Theorem for theBenchmark
% 0.21/0.60  % SZS output start Proof for theBenchmark
% 0.21/0.60  fof(f111,plain,(
% 0.21/0.60    $false),
% 0.21/0.60    inference(subsumption_resolution,[],[f110,f22])).
% 0.21/0.60  fof(f22,plain,(
% 0.21/0.60    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.60    inference(cnf_transformation,[],[f13])).
% 0.21/0.60  fof(f13,plain,(
% 0.21/0.60    (! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.21/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f7,f12,f11])).
% 0.21/0.60  fof(f11,plain,(
% 0.21/0.60    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f12,plain,(
% 0.21/0.60    ? [X4] : (! [X5] : (k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))) => (! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f7,plain,(
% 0.21/0.60    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.60    inference(flattening,[],[f6])).
% 0.21/0.60  fof(f6,plain,(
% 0.21/0.60    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.60    inference(ennf_transformation,[],[f5])).
% 0.21/0.60  fof(f5,negated_conjecture,(
% 0.21/0.60    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.60    inference(negated_conjecture,[],[f4])).
% 0.21/0.60  fof(f4,conjecture,(
% 0.21/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).
% 0.21/0.60  fof(f110,plain,(
% 0.21/0.60    ~v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.60    inference(subsumption_resolution,[],[f109,f23])).
% 0.21/0.60  fof(f23,plain,(
% 0.21/0.60    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.60    inference(cnf_transformation,[],[f13])).
% 0.21/0.60  fof(f109,plain,(
% 0.21/0.60    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.60    inference(resolution,[],[f91,f24])).
% 0.21/0.60  fof(f24,plain,(
% 0.21/0.60    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.60    inference(cnf_transformation,[],[f13])).
% 0.21/0.60  fof(f91,plain,(
% 0.21/0.60    ( ! [X0] : (~r2_hidden(sK4,k7_relset_1(sK0,X0,sK3,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_funct_2(sK3,sK0,X0)) )),
% 0.21/0.60    inference(subsumption_resolution,[],[f89,f64])).
% 0.21/0.60  fof(f64,plain,(
% 0.21/0.60    r2_hidden(sK6(sK0,sK2,sK3,sK4),sK2)),
% 0.21/0.60    inference(subsumption_resolution,[],[f63,f21])).
% 0.21/0.60  fof(f21,plain,(
% 0.21/0.60    v1_funct_1(sK3)),
% 0.21/0.60    inference(cnf_transformation,[],[f13])).
% 0.21/0.60  fof(f63,plain,(
% 0.21/0.60    r2_hidden(sK6(sK0,sK2,sK3,sK4),sK2) | ~v1_funct_1(sK3)),
% 0.21/0.60    inference(subsumption_resolution,[],[f62,f22])).
% 0.21/0.60  fof(f62,plain,(
% 0.21/0.60    r2_hidden(sK6(sK0,sK2,sK3,sK4),sK2) | ~v1_funct_2(sK3,sK0,sK1) | ~v1_funct_1(sK3)),
% 0.21/0.60    inference(subsumption_resolution,[],[f60,f23])).
% 0.21/0.60  fof(f60,plain,(
% 0.21/0.60    r2_hidden(sK6(sK0,sK2,sK3,sK4),sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK3,sK0,sK1) | ~v1_funct_1(sK3)),
% 0.21/0.60    inference(resolution,[],[f33,f24])).
% 0.21/0.60  fof(f33,plain,(
% 0.21/0.60    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) | r2_hidden(sK6(X0,X2,X3,X4),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f20])).
% 0.21/0.60  fof(f20,plain,(
% 0.21/0.60    ! [X0,X1,X2,X3] : (! [X4] : ((k1_funct_1(X3,sK6(X0,X2,X3,X4)) = X4 & r2_hidden(sK6(X0,X2,X3,X4),X2) & r2_hidden(sK6(X0,X2,X3,X4),X0)) | ~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f10,f19])).
% 0.21/0.60  fof(f19,plain,(
% 0.21/0.60    ! [X4,X3,X2,X0] : (? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) => (k1_funct_1(X3,sK6(X0,X2,X3,X4)) = X4 & r2_hidden(sK6(X0,X2,X3,X4),X2) & r2_hidden(sK6(X0,X2,X3,X4),X0)))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f10,plain,(
% 0.21/0.60    ! [X0,X1,X2,X3] : (! [X4] : (? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) | ~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.60    inference(flattening,[],[f9])).
% 0.21/0.60  fof(f9,plain,(
% 0.21/0.60    ! [X0,X1,X2,X3] : (! [X4] : (? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) | ~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.60    inference(ennf_transformation,[],[f3])).
% 0.21/0.60  fof(f3,axiom,(
% 0.21/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).
% 0.21/0.60  fof(f89,plain,(
% 0.21/0.60    ( ! [X0] : (~r2_hidden(sK6(sK0,sK2,sK3,sK4),sK2) | ~r2_hidden(sK4,k7_relset_1(sK0,X0,sK3,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_funct_2(sK3,sK0,X0)) )),
% 0.21/0.60    inference(resolution,[],[f76,f69])).
% 0.21/0.60  fof(f69,plain,(
% 0.21/0.60    m1_subset_1(sK6(sK0,sK2,sK3,sK4),sK0)),
% 0.21/0.60    inference(resolution,[],[f59,f35])).
% 0.21/0.60  fof(f35,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 0.21/0.60    inference(subsumption_resolution,[],[f29,f26])).
% 0.21/0.60  fof(f26,plain,(
% 0.21/0.60    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f17])).
% 0.21/0.60  fof(f17,plain,(
% 0.21/0.60    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK5(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f15,f16])).
% 0.21/0.60  fof(f16,plain,(
% 0.21/0.60    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f15,plain,(
% 0.21/0.60    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.60    inference(rectify,[],[f14])).
% 0.21/0.60  fof(f14,plain,(
% 0.21/0.60    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.60    inference(nnf_transformation,[],[f1])).
% 0.21/0.60  fof(f1,axiom,(
% 0.21/0.60    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.60  fof(f29,plain,(
% 0.21/0.60    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f18])).
% 0.21/0.60  fof(f18,plain,(
% 0.21/0.60    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.60    inference(nnf_transformation,[],[f8])).
% 0.21/0.60  fof(f8,plain,(
% 0.21/0.60    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.60    inference(ennf_transformation,[],[f2])).
% 0.21/0.60  fof(f2,axiom,(
% 0.21/0.60    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.60  fof(f59,plain,(
% 0.21/0.60    r2_hidden(sK6(sK0,sK2,sK3,sK4),sK0)),
% 0.21/0.60    inference(subsumption_resolution,[],[f58,f21])).
% 0.21/0.60  fof(f58,plain,(
% 0.21/0.60    r2_hidden(sK6(sK0,sK2,sK3,sK4),sK0) | ~v1_funct_1(sK3)),
% 0.21/0.60    inference(subsumption_resolution,[],[f57,f22])).
% 0.21/0.60  fof(f57,plain,(
% 0.21/0.60    r2_hidden(sK6(sK0,sK2,sK3,sK4),sK0) | ~v1_funct_2(sK3,sK0,sK1) | ~v1_funct_1(sK3)),
% 0.21/0.60    inference(subsumption_resolution,[],[f55,f23])).
% 0.21/0.60  fof(f55,plain,(
% 0.21/0.60    r2_hidden(sK6(sK0,sK2,sK3,sK4),sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK3,sK0,sK1) | ~v1_funct_1(sK3)),
% 0.21/0.60    inference(resolution,[],[f32,f24])).
% 0.21/0.60  fof(f32,plain,(
% 0.21/0.60    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) | r2_hidden(sK6(X0,X2,X3,X4),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f20])).
% 0.21/0.60  fof(f76,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(sK6(X0,X1,sK3,sK4),sK0) | ~r2_hidden(sK6(X0,X1,sK3,sK4),sK2) | ~r2_hidden(sK4,k7_relset_1(X0,X2,sK3,X1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(sK3,X0,X2)) )),
% 0.21/0.60    inference(equality_resolution,[],[f68])).
% 0.21/0.60  fof(f68,plain,(
% 0.21/0.60    ( ! [X2,X0,X3,X1] : (sK4 != X2 | ~r2_hidden(sK6(X0,X1,sK3,X2),sK2) | ~m1_subset_1(sK6(X0,X1,sK3,X2),sK0) | ~r2_hidden(X2,k7_relset_1(X0,X3,sK3,X1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~v1_funct_2(sK3,X0,X3)) )),
% 0.21/0.60    inference(subsumption_resolution,[],[f67,f21])).
% 0.21/0.60  fof(f67,plain,(
% 0.21/0.60    ( ! [X2,X0,X3,X1] : (sK4 != X2 | ~r2_hidden(sK6(X0,X1,sK3,X2),sK2) | ~m1_subset_1(sK6(X0,X1,sK3,X2),sK0) | ~r2_hidden(X2,k7_relset_1(X0,X3,sK3,X1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~v1_funct_2(sK3,X0,X3) | ~v1_funct_1(sK3)) )),
% 0.21/0.60    inference(superposition,[],[f25,f34])).
% 0.21/0.60  fof(f34,plain,(
% 0.21/0.60    ( ! [X4,X2,X0,X3,X1] : (k1_funct_1(X3,sK6(X0,X2,X3,X4)) = X4 | ~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f20])).
% 0.21/0.60  fof(f25,plain,(
% 0.21/0.60    ( ! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f13])).
% 0.21/0.60  % SZS output end Proof for theBenchmark
% 0.21/0.60  % (19484)------------------------------
% 0.21/0.60  % (19484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (19484)Termination reason: Refutation
% 0.21/0.60  
% 0.21/0.60  % (19484)Memory used [KB]: 10746
% 0.21/0.60  % (19484)Time elapsed: 0.057 s
% 0.21/0.60  % (19484)------------------------------
% 0.21/0.60  % (19484)------------------------------
% 0.21/0.60  % (19493)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.60  % (19348)Success in time 0.243 s
%------------------------------------------------------------------------------
