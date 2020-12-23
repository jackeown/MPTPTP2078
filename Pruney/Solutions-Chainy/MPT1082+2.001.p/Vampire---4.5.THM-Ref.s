%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   37 (  52 expanded)
%              Number of leaves         :    7 (  13 expanded)
%              Depth                    :   13
%              Number of atoms          :  148 ( 229 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f63,plain,(
    $false ),
    inference(subsumption_resolution,[],[f62,f19])).

fof(f19,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ m1_funct_2(k1_funct_2(sK0,sK1),sK0,sK1)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( ~ m1_funct_2(k1_funct_2(X0,X1),X0,X1)
        & ~ v1_xboole_0(X1) )
   => ( ~ m1_funct_2(k1_funct_2(sK0,sK1),sK0,sK1)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ~ m1_funct_2(k1_funct_2(X0,X1),X0,X1)
      & ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
       => m1_funct_2(k1_funct_2(X0,X1),X0,X1) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => m1_funct_2(k1_funct_2(X0,X1),X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t199_funct_2)).

fof(f62,plain,(
    v1_xboole_0(sK1) ),
    inference(resolution,[],[f55,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k1_funct_2(X0,X1))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k1_funct_2(X0,X1))
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ v1_xboole_0(k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_funct_2)).

fof(f55,plain,(
    v1_xboole_0(k1_funct_2(sK0,sK1)) ),
    inference(resolution,[],[f54,f20])).

fof(f20,plain,(
    ~ m1_funct_2(k1_funct_2(sK0,sK1),sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_funct_2(k1_funct_2(X0,X1),X0,X1)
      | v1_xboole_0(k1_funct_2(X0,X1)) ) ),
    inference(duplicate_literal_removal,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | m1_funct_2(k1_funct_2(X0,X1),X0,X1)
      | v1_xboole_0(k1_funct_2(X0,X1))
      | m1_funct_2(k1_funct_2(X0,X1),X0,X1) ) ),
    inference(resolution,[],[f52,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X1,X2,X0),X0)
      | v1_xboole_0(X0)
      | m1_funct_2(X0,X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( m1_funct_2(X0,X1,X2)
      | v1_xboole_0(X0)
      | r2_hidden(sK2(X1,X2,X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f29,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),X2)
      | m1_funct_2(X2,X0,X1)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ( m1_funct_2(X2,X0,X1)
          | ( ( ~ m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(sK2(X0,X1,X2),X0,X1)
              | ~ v1_funct_1(sK2(X0,X1,X2)) )
            & m1_subset_1(sK2(X0,X1,X2),X2) ) )
        & ( ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X4,X0,X1)
                & v1_funct_1(X4) )
              | ~ m1_subset_1(X4,X2) )
          | ~ m1_funct_2(X2,X0,X1) ) )
      | v1_xboole_0(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f17])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            | ~ v1_funct_2(X3,X0,X1)
            | ~ v1_funct_1(X3) )
          & m1_subset_1(X3,X2) )
     => ( ( ~ m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(sK2(X0,X1,X2),X0,X1)
          | ~ v1_funct_1(sK2(X0,X1,X2)) )
        & m1_subset_1(sK2(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( ( m1_funct_2(X2,X0,X1)
          | ? [X3] :
              ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                | ~ v1_funct_2(X3,X0,X1)
                | ~ v1_funct_1(X3) )
              & m1_subset_1(X3,X2) ) )
        & ( ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X4,X0,X1)
                & v1_funct_1(X4) )
              | ~ m1_subset_1(X4,X2) )
          | ~ m1_funct_2(X2,X0,X1) ) )
      | v1_xboole_0(X2) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( ( m1_funct_2(X2,X0,X1)
          | ? [X3] :
              ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                | ~ v1_funct_2(X3,X0,X1)
                | ~ v1_funct_1(X3) )
              & m1_subset_1(X3,X2) ) )
        & ( ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X3,X0,X1)
                & v1_funct_1(X3) )
              | ~ m1_subset_1(X3,X2) )
          | ~ m1_funct_2(X2,X0,X1) ) )
      | v1_xboole_0(X2) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( m1_funct_2(X2,X0,X1)
      <=> ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
            | ~ m1_subset_1(X3,X2) ) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ( m1_funct_2(X2,X0,X1)
      <=> ! [X3] :
            ( m1_subset_1(X3,X2)
           => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_2)).

fof(f52,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(sK2(X3,X4,X2),k1_funct_2(X3,X4))
      | v1_xboole_0(X2)
      | m1_funct_2(X2,X3,X4) ) ),
    inference(subsumption_resolution,[],[f51,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_funct_2(X0,X1))
      | v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

fof(f51,plain,(
    ! [X4,X2,X3] :
      ( m1_funct_2(X2,X3,X4)
      | ~ v1_funct_1(sK2(X3,X4,X2))
      | v1_xboole_0(X2)
      | ~ r2_hidden(sK2(X3,X4,X2),k1_funct_2(X3,X4)) ) ),
    inference(subsumption_resolution,[],[f48,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_funct_2(X0,X1))
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f48,plain,(
    ! [X4,X2,X3] :
      ( m1_funct_2(X2,X3,X4)
      | ~ v1_funct_2(sK2(X3,X4,X2),X3,X4)
      | ~ v1_funct_1(sK2(X3,X4,X2))
      | v1_xboole_0(X2)
      | ~ r2_hidden(sK2(X3,X4,X2),k1_funct_2(X3,X4)) ) ),
    inference(resolution,[],[f30,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_funct_2(X2,X0,X1)
      | ~ v1_funct_2(sK2(X0,X1,X2),X0,X1)
      | ~ v1_funct_1(sK2(X0,X1,X2))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:03:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (32508)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.21/0.46  % (32498)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.21/0.46  % (32508)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(subsumption_resolution,[],[f62,f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ~v1_xboole_0(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ~m1_funct_2(k1_funct_2(sK0,sK1),sK0,sK1) & ~v1_xboole_0(sK1)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ? [X0,X1] : (~m1_funct_2(k1_funct_2(X0,X1),X0,X1) & ~v1_xboole_0(X1)) => (~m1_funct_2(k1_funct_2(sK0,sK1),sK0,sK1) & ~v1_xboole_0(sK1))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    ? [X0,X1] : (~m1_funct_2(k1_funct_2(X0,X1),X0,X1) & ~v1_xboole_0(X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1] : (~v1_xboole_0(X1) => m1_funct_2(k1_funct_2(X0,X1),X0,X1))),
% 0.21/0.46    inference(negated_conjecture,[],[f5])).
% 0.21/0.46  fof(f5,conjecture,(
% 0.21/0.46    ! [X0,X1] : (~v1_xboole_0(X1) => m1_funct_2(k1_funct_2(X0,X1),X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t199_funct_2)).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    v1_xboole_0(sK1)),
% 0.21/0.46    inference(resolution,[],[f55,f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_xboole_0(k1_funct_2(X0,X1)) | v1_xboole_0(X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ! [X0,X1] : (~v1_xboole_0(k1_funct_2(X0,X1)) | v1_xboole_0(X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : (~v1_xboole_0(X1) => ~v1_xboole_0(k1_funct_2(X0,X1)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_funct_2)).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    v1_xboole_0(k1_funct_2(sK0,sK1))),
% 0.21/0.46    inference(resolution,[],[f54,f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ~m1_funct_2(k1_funct_2(sK0,sK1),sK0,sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    ( ! [X0,X1] : (m1_funct_2(k1_funct_2(X0,X1),X0,X1) | v1_xboole_0(k1_funct_2(X0,X1))) )),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f53])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    ( ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | m1_funct_2(k1_funct_2(X0,X1),X0,X1) | v1_xboole_0(k1_funct_2(X0,X1)) | m1_funct_2(k1_funct_2(X0,X1),X0,X1)) )),
% 0.21/0.46    inference(resolution,[],[f52,f41])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (r2_hidden(sK2(X1,X2,X0),X0) | v1_xboole_0(X0) | m1_funct_2(X0,X1,X2)) )),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f39])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (m1_funct_2(X0,X1,X2) | v1_xboole_0(X0) | r2_hidden(sK2(X1,X2,X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.46    inference(resolution,[],[f29,f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.46    inference(nnf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),X2) | m1_funct_2(X2,X0,X1) | v1_xboole_0(X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (((m1_funct_2(X2,X0,X1) | ((~m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2(X0,X1,X2),X0,X1) | ~v1_funct_1(sK2(X0,X1,X2))) & m1_subset_1(sK2(X0,X1,X2),X2))) & (! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4)) | ~m1_subset_1(X4,X2)) | ~m1_funct_2(X2,X0,X1))) | v1_xboole_0(X2))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X2,X1,X0] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) & m1_subset_1(X3,X2)) => ((~m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2(X0,X1,X2),X0,X1) | ~v1_funct_1(sK2(X0,X1,X2))) & m1_subset_1(sK2(X0,X1,X2),X2)))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (((m1_funct_2(X2,X0,X1) | ? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) & m1_subset_1(X3,X2))) & (! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4)) | ~m1_subset_1(X4,X2)) | ~m1_funct_2(X2,X0,X1))) | v1_xboole_0(X2))),
% 0.21/0.46    inference(rectify,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (((m1_funct_2(X2,X0,X1) | ? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) & m1_subset_1(X3,X2))) & (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~m1_subset_1(X3,X2)) | ~m1_funct_2(X2,X0,X1))) | v1_xboole_0(X2))),
% 0.21/0.46    inference(nnf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((m1_funct_2(X2,X0,X1) <=> ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~m1_subset_1(X3,X2))) | v1_xboole_0(X2))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (~v1_xboole_0(X2) => (m1_funct_2(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,X2) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_2)).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    ( ! [X4,X2,X3] : (~r2_hidden(sK2(X3,X4,X2),k1_funct_2(X3,X4)) | v1_xboole_0(X2) | m1_funct_2(X2,X3,X4)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f51,f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_funct_2(X0,X1)) | v1_funct_1(X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~r2_hidden(X2,k1_funct_2(X0,X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    ( ! [X4,X2,X3] : (m1_funct_2(X2,X3,X4) | ~v1_funct_1(sK2(X3,X4,X2)) | v1_xboole_0(X2) | ~r2_hidden(sK2(X3,X4,X2),k1_funct_2(X3,X4))) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f48,f32])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_funct_2(X0,X1)) | v1_funct_2(X2,X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    ( ! [X4,X2,X3] : (m1_funct_2(X2,X3,X4) | ~v1_funct_2(sK2(X3,X4,X2),X3,X4) | ~v1_funct_1(sK2(X3,X4,X2)) | v1_xboole_0(X2) | ~r2_hidden(sK2(X3,X4,X2),k1_funct_2(X3,X4))) )),
% 0.21/0.46    inference(resolution,[],[f30,f33])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_funct_2(X2,X0,X1) | ~v1_funct_2(sK2(X0,X1,X2),X0,X1) | ~v1_funct_1(sK2(X0,X1,X2)) | v1_xboole_0(X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f18])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (32508)------------------------------
% 0.21/0.46  % (32508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (32508)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (32508)Memory used [KB]: 5373
% 0.21/0.46  % (32508)Time elapsed: 0.048 s
% 0.21/0.46  % (32508)------------------------------
% 0.21/0.46  % (32508)------------------------------
% 0.21/0.46  % (32498)Refutation not found, incomplete strategy% (32498)------------------------------
% 0.21/0.46  % (32498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (32498)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (32498)Memory used [KB]: 9850
% 0.21/0.46  % (32498)Time elapsed: 0.045 s
% 0.21/0.46  % (32498)------------------------------
% 0.21/0.46  % (32498)------------------------------
% 0.21/0.47  % (32488)Success in time 0.107 s
%------------------------------------------------------------------------------
