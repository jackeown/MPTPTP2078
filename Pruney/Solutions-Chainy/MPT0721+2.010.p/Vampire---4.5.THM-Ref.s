%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:06 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   23 (  44 expanded)
%              Number of leaves         :    4 (   9 expanded)
%              Depth                    :    7
%              Number of atoms          :   66 ( 167 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f28,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f15,f13,f16,f23,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

fof(f23,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK1),k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f21,f14,f13,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X2,k2_relat_1(X1))
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k2_relat_1(X1))
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t202_relat_1)).

fof(f14,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ m1_subset_1(k1_funct_1(X2,X1),X0)
      & r2_hidden(X1,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v5_relat_1(X2,X0)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ m1_subset_1(k1_funct_1(X2,X1),X0)
      & r2_hidden(X1,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v5_relat_1(X2,X0)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
       => ( r2_hidden(X1,k1_relat_1(X2))
         => m1_subset_1(k1_funct_1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v5_relat_1(X2,X0)
        & v1_relat_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => m1_subset_1(k1_funct_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).

fof(f21,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f17,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f17,plain,(
    ~ m1_subset_1(k1_funct_1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f16,plain,(
    r2_hidden(sK1,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f13,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f15,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:10:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.37  ipcrm: permission denied for id (811991042)
% 0.21/0.37  ipcrm: permission denied for id (812023811)
% 0.21/0.40  ipcrm: permission denied for id (812220437)
% 0.21/0.43  ipcrm: permission denied for id (812285988)
% 0.21/0.44  ipcrm: permission denied for id (812351531)
% 0.21/0.44  ipcrm: permission denied for id (812384304)
% 0.21/0.45  ipcrm: permission denied for id (812417073)
% 0.21/0.47  ipcrm: permission denied for id (812515390)
% 0.21/0.48  ipcrm: permission denied for id (812580937)
% 0.21/0.49  ipcrm: permission denied for id (812646480)
% 0.21/0.50  ipcrm: permission denied for id (812679258)
% 0.21/0.50  ipcrm: permission denied for id (812744801)
% 0.21/0.51  ipcrm: permission denied for id (812777581)
% 0.21/0.51  ipcrm: permission denied for id (812843120)
% 0.21/0.52  ipcrm: permission denied for id (812908662)
% 0.37/0.60  % (678)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.37/0.60  % (678)Refutation found. Thanks to Tanya!
% 0.37/0.60  % SZS status Theorem for theBenchmark
% 0.37/0.60  % SZS output start Proof for theBenchmark
% 0.37/0.60  fof(f28,plain,(
% 0.37/0.60    $false),
% 0.37/0.60    inference(unit_resulting_resolution,[],[f15,f13,f16,f23,f19])).
% 0.37/0.60  fof(f19,plain,(
% 0.37/0.60    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))) )),
% 0.37/0.60    inference(cnf_transformation,[],[f10])).
% 0.37/0.60  fof(f10,plain,(
% 0.37/0.60    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.37/0.60    inference(flattening,[],[f9])).
% 0.37/0.60  fof(f9,plain,(
% 0.37/0.60    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.37/0.60    inference(ennf_transformation,[],[f3])).
% 0.37/0.60  fof(f3,axiom,(
% 0.37/0.60    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 0.37/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).
% 0.37/0.60  fof(f23,plain,(
% 0.37/0.60    ~r2_hidden(k1_funct_1(sK2,sK1),k2_relat_1(sK2))),
% 0.37/0.60    inference(unit_resulting_resolution,[],[f21,f14,f13,f20])).
% 0.37/0.60  fof(f20,plain,(
% 0.37/0.60    ( ! [X2,X0,X1] : (~v5_relat_1(X1,X0) | ~v1_relat_1(X1) | ~r2_hidden(X2,k2_relat_1(X1)) | r2_hidden(X2,X0)) )),
% 0.37/0.60    inference(cnf_transformation,[],[f12])).
% 0.37/0.60  fof(f12,plain,(
% 0.37/0.60    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.37/0.60    inference(flattening,[],[f11])).
% 0.37/0.60  fof(f11,plain,(
% 0.37/0.60    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1))) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.37/0.60    inference(ennf_transformation,[],[f2])).
% 0.37/0.60  fof(f2,axiom,(
% 0.37/0.60    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k2_relat_1(X1)) => r2_hidden(X2,X0)))),
% 0.37/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t202_relat_1)).
% 0.37/0.60  fof(f14,plain,(
% 0.37/0.60    v5_relat_1(sK2,sK0)),
% 0.37/0.60    inference(cnf_transformation,[],[f7])).
% 0.37/0.60  fof(f7,plain,(
% 0.37/0.60    ? [X0,X1,X2] : (~m1_subset_1(k1_funct_1(X2,X1),X0) & r2_hidden(X1,k1_relat_1(X2)) & v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2))),
% 0.37/0.60    inference(flattening,[],[f6])).
% 0.37/0.60  fof(f6,plain,(
% 0.37/0.60    ? [X0,X1,X2] : ((~m1_subset_1(k1_funct_1(X2,X1),X0) & r2_hidden(X1,k1_relat_1(X2))) & (v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)))),
% 0.37/0.60    inference(ennf_transformation,[],[f5])).
% 0.37/0.60  fof(f5,negated_conjecture,(
% 0.37/0.60    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (r2_hidden(X1,k1_relat_1(X2)) => m1_subset_1(k1_funct_1(X2,X1),X0)))),
% 0.37/0.60    inference(negated_conjecture,[],[f4])).
% 0.37/0.60  fof(f4,conjecture,(
% 0.37/0.60    ! [X0,X1,X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (r2_hidden(X1,k1_relat_1(X2)) => m1_subset_1(k1_funct_1(X2,X1),X0)))),
% 0.37/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).
% 0.37/0.60  fof(f21,plain,(
% 0.37/0.60    ~r2_hidden(k1_funct_1(sK2,sK1),sK0)),
% 0.37/0.60    inference(unit_resulting_resolution,[],[f17,f18])).
% 0.37/0.60  fof(f18,plain,(
% 0.37/0.60    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.37/0.60    inference(cnf_transformation,[],[f8])).
% 0.37/0.60  fof(f8,plain,(
% 0.37/0.60    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.37/0.60    inference(ennf_transformation,[],[f1])).
% 0.37/0.60  fof(f1,axiom,(
% 0.37/0.60    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.37/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.37/0.60  fof(f17,plain,(
% 0.37/0.60    ~m1_subset_1(k1_funct_1(sK2,sK1),sK0)),
% 0.37/0.60    inference(cnf_transformation,[],[f7])).
% 0.37/0.60  fof(f16,plain,(
% 0.37/0.60    r2_hidden(sK1,k1_relat_1(sK2))),
% 0.37/0.60    inference(cnf_transformation,[],[f7])).
% 0.37/0.60  fof(f13,plain,(
% 0.37/0.60    v1_relat_1(sK2)),
% 0.37/0.60    inference(cnf_transformation,[],[f7])).
% 0.37/0.60  fof(f15,plain,(
% 0.37/0.60    v1_funct_1(sK2)),
% 0.37/0.60    inference(cnf_transformation,[],[f7])).
% 0.37/0.60  % SZS output end Proof for theBenchmark
% 0.37/0.60  % (678)------------------------------
% 0.37/0.60  % (678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.37/0.60  % (678)Termination reason: Refutation
% 0.37/0.60  
% 0.37/0.60  % (678)Memory used [KB]: 767
% 0.37/0.60  % (678)Time elapsed: 0.003 s
% 0.37/0.60  % (678)------------------------------
% 0.37/0.60  % (678)------------------------------
% 0.37/0.60  % (464)Success in time 0.235 s
%------------------------------------------------------------------------------
