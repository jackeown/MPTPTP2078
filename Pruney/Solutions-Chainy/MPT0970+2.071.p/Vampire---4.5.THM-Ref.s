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
% DateTime   : Thu Dec  3 13:00:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 185 expanded)
%              Number of leaves         :    7 (  40 expanded)
%              Depth                    :   16
%              Number of atoms          :  153 ( 682 expanded)
%              Number of equality atoms :   32 ( 140 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f236,plain,(
    $false ),
    inference(subsumption_resolution,[],[f206,f22])).

fof(f22,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f206,plain,(
    ~ r1_tarski(k1_xboole_0,k2_relset_1(sK0,k1_xboole_0,sK2)) ),
    inference(backward_demodulation,[],[f83,f179])).

fof(f179,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f176,f83])).

fof(f176,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(sK1,k2_relset_1(sK0,sK1,sK2)) ),
    inference(resolution,[],[f150,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f150,plain,
    ( r2_hidden(sK4(sK1,k2_relset_1(sK0,sK1,sK2)),k2_relset_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f147,f83])).

fof(f147,plain,
    ( r2_hidden(sK4(sK1,k2_relset_1(sK0,sK1,sK2)),k2_relset_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK1
    | r1_tarski(sK1,k2_relset_1(sK0,sK1,sK2)) ),
    inference(superposition,[],[f125,f82])).

fof(f82,plain,(
    sK4(sK1,k2_relset_1(sK0,sK1,sK2)) = k1_funct_1(sK2,sK3(sK4(sK1,k2_relset_1(sK0,sK1,sK2)))) ),
    inference(subsumption_resolution,[],[f79,f21])).

fof(f21,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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

fof(f79,plain,
    ( sK4(sK1,k2_relset_1(sK0,sK1,sK2)) = k1_funct_1(sK2,sK3(sK4(sK1,k2_relset_1(sK0,sK1,sK2))))
    | sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f78,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | sK4(sK1,X0) = k1_funct_1(sK2,sK3(sK4(sK1,X0)))
      | sK1 = X0 ) ),
    inference(resolution,[],[f34,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f34,plain,(
    ! [X0] :
      ( r1_tarski(sK1,X0)
      | sK4(sK1,X0) = k1_funct_1(sK2,sK3(sK4(sK1,X0))) ) ),
    inference(resolution,[],[f28,f17])).

fof(f17,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | k1_funct_1(sK2,sK3(X3)) = X3 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f78,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK2),sK1) ),
    inference(duplicate_literal_removal,[],[f74])).

fof(f74,plain,
    ( r1_tarski(k2_relset_1(sK0,sK1,sK2),sK1)
    | r1_tarski(k2_relset_1(sK0,sK1,sK2),sK1) ),
    inference(resolution,[],[f72,f29])).

fof(f72,plain,(
    ! [X0] :
      ( r2_hidden(sK4(k2_relset_1(sK0,sK1,sK2),X0),sK1)
      | r1_tarski(k2_relset_1(sK0,sK1,sK2),X0) ) ),
    inference(resolution,[],[f70,f28])).

fof(f70,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relset_1(sK0,sK1,sK2))
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f48,f20])).

fof(f20,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f10])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r2_hidden(X3,k2_relset_1(X1,X2,X0))
      | r2_hidden(X3,X2) ) ),
    inference(resolution,[],[f30,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f125,plain,(
    ! [X1] :
      ( r2_hidden(k1_funct_1(sK2,sK3(sK4(sK1,X1))),k2_relset_1(sK0,sK1,sK2))
      | k1_xboole_0 = sK1
      | r1_tarski(sK1,X1) ) ),
    inference(resolution,[],[f123,f44])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK4(sK1,X0)),sK0)
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f43,f32])).

fof(f32,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK0,X0)
      | r2_hidden(sK3(sK4(sK1,X1)),X0)
      | r1_tarski(sK1,X1) ) ),
    inference(resolution,[],[f41,f28])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r1_tarski(sK0,X1)
      | r2_hidden(sK3(X0),X1) ) ),
    inference(resolution,[],[f27,f16])).

fof(f16,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f123,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK1
      | r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(sK0,sK1,sK2)) ) ),
    inference(subsumption_resolution,[],[f122,f19])).

fof(f19,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f122,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,sK0,sK1)
      | ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK1
      | r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(sK0,sK1,sK2)) ) ),
    inference(resolution,[],[f87,f20])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | r2_hidden(k1_funct_1(sK2,X2),k2_relset_1(X0,X1,sK2)) ) ),
    inference(resolution,[],[f31,f18])).

fof(f18,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

fof(f83,plain,(
    ~ r1_tarski(sK1,k2_relset_1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f81,f21])).

fof(f81,plain,
    ( ~ r1_tarski(sK1,k2_relset_1(sK0,sK1,sK2))
    | sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f78,f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:09:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.45  % (4595)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.48  % (4595)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (4612)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f236,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(subsumption_resolution,[],[f206,f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.50  fof(f206,plain,(
% 0.21/0.50    ~r1_tarski(k1_xboole_0,k2_relset_1(sK0,k1_xboole_0,sK2))),
% 0.21/0.50    inference(backward_demodulation,[],[f83,f179])).
% 0.21/0.50  fof(f179,plain,(
% 0.21/0.50    k1_xboole_0 = sK1),
% 0.21/0.50    inference(subsumption_resolution,[],[f176,f83])).
% 0.21/0.50  fof(f176,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | r1_tarski(sK1,k2_relset_1(sK0,sK1,sK2))),
% 0.21/0.50    inference(resolution,[],[f150,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    r2_hidden(sK4(sK1,k2_relset_1(sK0,sK1,sK2)),k2_relset_1(sK0,sK1,sK2)) | k1_xboole_0 = sK1),
% 0.21/0.50    inference(subsumption_resolution,[],[f147,f83])).
% 0.21/0.50  fof(f147,plain,(
% 0.21/0.50    r2_hidden(sK4(sK1,k2_relset_1(sK0,sK1,sK2)),k2_relset_1(sK0,sK1,sK2)) | k1_xboole_0 = sK1 | r1_tarski(sK1,k2_relset_1(sK0,sK1,sK2))),
% 0.21/0.50    inference(superposition,[],[f125,f82])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    sK4(sK1,k2_relset_1(sK0,sK1,sK2)) = k1_funct_1(sK2,sK3(sK4(sK1,k2_relset_1(sK0,sK1,sK2))))),
% 0.21/0.50    inference(subsumption_resolution,[],[f79,f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.50    inference(flattening,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.50    inference(negated_conjecture,[],[f7])).
% 0.21/0.50  fof(f7,conjecture,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    sK4(sK1,k2_relset_1(sK0,sK1,sK2)) = k1_funct_1(sK2,sK3(sK4(sK1,k2_relset_1(sK0,sK1,sK2)))) | sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.50    inference(resolution,[],[f78,f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(X0,sK1) | sK4(sK1,X0) = k1_funct_1(sK2,sK3(sK4(sK1,X0))) | sK1 = X0) )),
% 0.21/0.50    inference(resolution,[],[f34,f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(sK1,X0) | sK4(sK1,X0) = k1_funct_1(sK2,sK3(sK4(sK1,X0)))) )),
% 0.21/0.50    inference(resolution,[],[f28,f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ( ! [X3] : (~r2_hidden(X3,sK1) | k1_funct_1(sK2,sK3(X3)) = X3) )),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    r1_tarski(k2_relset_1(sK0,sK1,sK2),sK1)),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f74])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    r1_tarski(k2_relset_1(sK0,sK1,sK2),sK1) | r1_tarski(k2_relset_1(sK0,sK1,sK2),sK1)),
% 0.21/0.50    inference(resolution,[],[f72,f29])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK4(k2_relset_1(sK0,sK1,sK2),X0),sK1) | r1_tarski(k2_relset_1(sK0,sK1,sK2),X0)) )),
% 0.21/0.50    inference(resolution,[],[f70,f28])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k2_relset_1(sK0,sK1,sK2)) | r2_hidden(X0,sK1)) )),
% 0.21/0.50    inference(resolution,[],[f48,f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r2_hidden(X3,k2_relset_1(X1,X2,X0)) | r2_hidden(X3,X2)) )),
% 0.21/0.50    inference(resolution,[],[f30,f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    ( ! [X1] : (r2_hidden(k1_funct_1(sK2,sK3(sK4(sK1,X1))),k2_relset_1(sK0,sK1,sK2)) | k1_xboole_0 = sK1 | r1_tarski(sK1,X1)) )),
% 0.21/0.50    inference(resolution,[],[f123,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK3(sK4(sK1,X0)),sK0) | r1_tarski(sK1,X0)) )),
% 0.21/0.50    inference(resolution,[],[f43,f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.50    inference(equality_resolution,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(sK0,X0) | r2_hidden(sK3(sK4(sK1,X1)),X0) | r1_tarski(sK1,X1)) )),
% 0.21/0.50    inference(resolution,[],[f41,f28])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | ~r1_tarski(sK0,X1) | r2_hidden(sK3(X0),X1)) )),
% 0.21/0.50    inference(resolution,[],[f27,f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ( ! [X3] : (r2_hidden(sK3(X3),sK0) | ~r2_hidden(X3,sK1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_xboole_0 = sK1 | r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(sK0,sK1,sK2))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f122,f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_funct_2(sK2,sK0,sK1) | ~r2_hidden(X0,sK0) | k1_xboole_0 = sK1 | r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(sK0,sK1,sK2))) )),
% 0.21/0.50    inference(resolution,[],[f87,f20])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | r2_hidden(k1_funct_1(sK2,X2),k2_relset_1(X0,X1,sK2))) )),
% 0.21/0.50    inference(resolution,[],[f31,f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    v1_funct_1(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.50    inference(flattening,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    ~r1_tarski(sK1,k2_relset_1(sK0,sK1,sK2))),
% 0.21/0.50    inference(subsumption_resolution,[],[f81,f21])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    ~r1_tarski(sK1,k2_relset_1(sK0,sK1,sK2)) | sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.50    inference(resolution,[],[f78,f26])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (4595)------------------------------
% 0.21/0.50  % (4595)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (4595)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (4595)Memory used [KB]: 6396
% 0.21/0.50  % (4595)Time elapsed: 0.089 s
% 0.21/0.50  % (4595)------------------------------
% 0.21/0.50  % (4595)------------------------------
% 0.21/0.50  % (4604)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.50  % (4588)Success in time 0.15 s
%------------------------------------------------------------------------------
