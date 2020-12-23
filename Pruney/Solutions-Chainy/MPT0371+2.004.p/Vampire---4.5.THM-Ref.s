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
% DateTime   : Thu Dec  3 12:45:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   34 ( 157 expanded)
%              Number of leaves         :    2 (  27 expanded)
%              Depth                    :   22
%              Number of atoms          :  122 ( 752 expanded)
%              Number of equality atoms :   26 ( 136 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f69,plain,(
    $false ),
    inference(subsumption_resolution,[],[f68,f11])).

fof(f11,plain,(
    sK1 != k3_subset_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( ~ r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( ~ r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( ~ r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
             => k3_subset_1(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( ~ r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_subset_1)).

fof(f68,plain,(
    sK1 = k3_subset_1(sK0,sK2) ),
    inference(subsumption_resolution,[],[f67,f10])).

fof(f10,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f67,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | sK1 = k3_subset_1(sK0,sK2) ),
    inference(subsumption_resolution,[],[f66,f12])).

fof(f12,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f66,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | sK1 = k3_subset_1(sK0,sK2) ),
    inference(resolution,[],[f65,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(sK3(X0,X1,X2),X0)
      | k3_subset_1(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,X2) = X1
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> ~ r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,X2) = X1
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> ~ r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> ~ r2_hidden(X3,X2) ) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_subset_1)).

fof(f65,plain,(
    ~ m1_subset_1(sK3(sK0,sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f64,f11])).

fof(f64,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK2),sK0)
    | sK1 = k3_subset_1(sK0,sK2) ),
    inference(subsumption_resolution,[],[f63,f59])).

fof(f59,plain,(
    r2_hidden(sK3(sK0,sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f58,f11])).

fof(f58,plain,
    ( r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | sK1 = k3_subset_1(sK0,sK2) ),
    inference(subsumption_resolution,[],[f57,f10])).

fof(f57,plain,
    ( r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | sK1 = k3_subset_1(sK0,sK2) ),
    inference(subsumption_resolution,[],[f56,f12])).

fof(f56,plain,
    ( r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | sK1 = k3_subset_1(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f54])).

fof(f54,plain,
    ( r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | sK1 = k3_subset_1(sK0,sK2) ),
    inference(resolution,[],[f53,f13])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | k3_subset_1(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f53,plain,
    ( r2_hidden(sK3(sK0,sK1,sK2),sK2)
    | r2_hidden(sK3(sK0,sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f51,f11])).

fof(f51,plain,
    ( r2_hidden(sK3(sK0,sK1,sK2),sK2)
    | r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | sK1 = k3_subset_1(sK0,sK2) ),
    inference(resolution,[],[f36,f10])).

fof(f36,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(sK0))
      | r2_hidden(sK3(sK0,sK1,X4),sK2)
      | r2_hidden(sK3(sK0,sK1,X4),sK1)
      | sK1 = k3_subset_1(sK0,X4) ) ),
    inference(resolution,[],[f33,f12])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | r2_hidden(sK3(sK0,X0,X1),sK1)
      | r2_hidden(sK3(sK0,X0,X1),sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | k3_subset_1(sK0,X1) = X0 ) ),
    inference(resolution,[],[f9,f15])).

fof(f9,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | r2_hidden(X3,sK2)
      | r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f63,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK2),sK0)
    | ~ r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | sK1 = k3_subset_1(sK0,sK2) ),
    inference(subsumption_resolution,[],[f62,f10])).

fof(f62,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | sK1 = k3_subset_1(sK0,sK2) ),
    inference(subsumption_resolution,[],[f60,f12])).

fof(f60,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK2),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | sK1 = k3_subset_1(sK0,sK2) ),
    inference(resolution,[],[f59,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,sK2),sK1)
      | ~ m1_subset_1(sK3(X0,X1,sK2),sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ r2_hidden(sK3(X0,X1,sK2),X1)
      | k3_subset_1(X0,sK2) = X1 ) ),
    inference(resolution,[],[f8,f14])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | k3_subset_1(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK2)
      | ~ m1_subset_1(X3,sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f5])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:00:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (7096)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.42  % (7096)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f69,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(subsumption_resolution,[],[f68,f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    sK1 != k3_subset_1(sK0,sK2)),
% 0.21/0.42    inference(cnf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,plain,(
% 0.21/0.42    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & ! [X3] : ((~r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.42    inference(flattening,[],[f4])).
% 0.21/0.42  fof(f4,plain,(
% 0.21/0.42    ? [X0,X1] : (? [X2] : ((k3_subset_1(X0,X2) != X1 & ! [X3] : ((~r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (~r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => k3_subset_1(X0,X2) = X1)))),
% 0.21/0.42    inference(negated_conjecture,[],[f2])).
% 0.21/0.42  fof(f2,conjecture,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (~r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => k3_subset_1(X0,X2) = X1)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_subset_1)).
% 0.21/0.42  fof(f68,plain,(
% 0.21/0.42    sK1 = k3_subset_1(sK0,sK2)),
% 0.21/0.42    inference(subsumption_resolution,[],[f67,f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.42    inference(cnf_transformation,[],[f5])).
% 0.21/0.42  fof(f67,plain,(
% 0.21/0.42    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | sK1 = k3_subset_1(sK0,sK2)),
% 0.21/0.42    inference(subsumption_resolution,[],[f66,f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.42    inference(cnf_transformation,[],[f5])).
% 0.21/0.42  fof(f66,plain,(
% 0.21/0.42    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | sK1 = k3_subset_1(sK0,sK2)),
% 0.21/0.42    inference(resolution,[],[f65,f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(sK3(X0,X1,X2),X0) | k3_subset_1(X0,X2) = X1) )),
% 0.21/0.42    inference(cnf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,plain,(
% 0.21/0.42    ! [X0,X1] : (! [X2] : (k3_subset_1(X0,X2) = X1 | ? [X3] : ((r2_hidden(X3,X1) <~> ~r2_hidden(X3,X2)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.42    inference(flattening,[],[f6])).
% 0.21/0.42  fof(f6,plain,(
% 0.21/0.42    ! [X0,X1] : (! [X2] : ((k3_subset_1(X0,X2) = X1 | ? [X3] : ((r2_hidden(X3,X1) <~> ~r2_hidden(X3,X2)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> ~r2_hidden(X3,X2))) => k3_subset_1(X0,X2) = X1)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_subset_1)).
% 0.21/0.42  fof(f65,plain,(
% 0.21/0.42    ~m1_subset_1(sK3(sK0,sK1,sK2),sK0)),
% 0.21/0.42    inference(subsumption_resolution,[],[f64,f11])).
% 0.21/0.42  fof(f64,plain,(
% 0.21/0.42    ~m1_subset_1(sK3(sK0,sK1,sK2),sK0) | sK1 = k3_subset_1(sK0,sK2)),
% 0.21/0.42    inference(subsumption_resolution,[],[f63,f59])).
% 0.21/0.42  fof(f59,plain,(
% 0.21/0.42    r2_hidden(sK3(sK0,sK1,sK2),sK1)),
% 0.21/0.42    inference(subsumption_resolution,[],[f58,f11])).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    r2_hidden(sK3(sK0,sK1,sK2),sK1) | sK1 = k3_subset_1(sK0,sK2)),
% 0.21/0.42    inference(subsumption_resolution,[],[f57,f10])).
% 0.21/0.42  fof(f57,plain,(
% 0.21/0.42    r2_hidden(sK3(sK0,sK1,sK2),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | sK1 = k3_subset_1(sK0,sK2)),
% 0.21/0.42    inference(subsumption_resolution,[],[f56,f12])).
% 0.21/0.42  fof(f56,plain,(
% 0.21/0.42    r2_hidden(sK3(sK0,sK1,sK2),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | sK1 = k3_subset_1(sK0,sK2)),
% 0.21/0.42    inference(duplicate_literal_removal,[],[f54])).
% 0.21/0.42  fof(f54,plain,(
% 0.21/0.42    r2_hidden(sK3(sK0,sK1,sK2),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | r2_hidden(sK3(sK0,sK1,sK2),sK1) | sK1 = k3_subset_1(sK0,sK2)),
% 0.21/0.42    inference(resolution,[],[f53,f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1) | k3_subset_1(X0,X2) = X1) )),
% 0.21/0.42    inference(cnf_transformation,[],[f7])).
% 0.21/0.42  fof(f53,plain,(
% 0.21/0.42    r2_hidden(sK3(sK0,sK1,sK2),sK2) | r2_hidden(sK3(sK0,sK1,sK2),sK1)),
% 0.21/0.42    inference(subsumption_resolution,[],[f51,f11])).
% 0.21/0.42  fof(f51,plain,(
% 0.21/0.42    r2_hidden(sK3(sK0,sK1,sK2),sK2) | r2_hidden(sK3(sK0,sK1,sK2),sK1) | sK1 = k3_subset_1(sK0,sK2)),
% 0.21/0.42    inference(resolution,[],[f36,f10])).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(sK0)) | r2_hidden(sK3(sK0,sK1,X4),sK2) | r2_hidden(sK3(sK0,sK1,X4),sK1) | sK1 = k3_subset_1(sK0,X4)) )),
% 0.21/0.42    inference(resolution,[],[f33,f12])).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | r2_hidden(sK3(sK0,X0,X1),sK1) | r2_hidden(sK3(sK0,X0,X1),sK2) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | k3_subset_1(sK0,X1) = X0) )),
% 0.21/0.42    inference(resolution,[],[f9,f15])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ( ! [X3] : (~m1_subset_1(X3,sK0) | r2_hidden(X3,sK2) | r2_hidden(X3,sK1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f5])).
% 0.21/0.42  fof(f63,plain,(
% 0.21/0.42    ~m1_subset_1(sK3(sK0,sK1,sK2),sK0) | ~r2_hidden(sK3(sK0,sK1,sK2),sK1) | sK1 = k3_subset_1(sK0,sK2)),
% 0.21/0.42    inference(subsumption_resolution,[],[f62,f10])).
% 0.21/0.42  fof(f62,plain,(
% 0.21/0.42    ~m1_subset_1(sK3(sK0,sK1,sK2),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~r2_hidden(sK3(sK0,sK1,sK2),sK1) | sK1 = k3_subset_1(sK0,sK2)),
% 0.21/0.42    inference(subsumption_resolution,[],[f60,f12])).
% 0.21/0.42  fof(f60,plain,(
% 0.21/0.42    ~m1_subset_1(sK3(sK0,sK1,sK2),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~r2_hidden(sK3(sK0,sK1,sK2),sK1) | sK1 = k3_subset_1(sK0,sK2)),
% 0.21/0.42    inference(resolution,[],[f59,f31])).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1,sK2),sK1) | ~m1_subset_1(sK3(X0,X1,sK2),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~r2_hidden(sK3(X0,X1,sK2),X1) | k3_subset_1(X0,sK2) = X1) )),
% 0.21/0.42    inference(resolution,[],[f8,f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1) | k3_subset_1(X0,X2) = X1) )),
% 0.21/0.42    inference(cnf_transformation,[],[f7])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ( ! [X3] : (~r2_hidden(X3,sK2) | ~m1_subset_1(X3,sK0) | ~r2_hidden(X3,sK1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f5])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (7096)------------------------------
% 0.21/0.42  % (7096)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (7096)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (7096)Memory used [KB]: 1663
% 0.21/0.42  % (7096)Time elapsed: 0.005 s
% 0.21/0.42  % (7096)------------------------------
% 0.21/0.42  % (7096)------------------------------
% 0.21/0.42  % (7082)Success in time 0.066 s
%------------------------------------------------------------------------------
