%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   15 (  39 expanded)
%              Number of leaves         :    2 (   8 expanded)
%              Depth                    :   10
%              Number of atoms          :   53 ( 191 expanded)
%              Number of equality atoms :   20 (  74 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,plain,(
    $false ),
    inference(subsumption_resolution,[],[f14,f11])).

fof(f11,plain,(
    m1_setfam_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,
    ( ~ m1_setfam_1(sK3,u1_struct_0(sK1))
    & m1_setfam_1(sK2,u1_struct_0(sK0))
    & sK2 = sK3
    & u1_struct_0(sK1) = u1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f6,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_setfam_1(X3,u1_struct_0(X1))
        & m1_setfam_1(X2,u1_struct_0(X0))
        & X2 = X3
        & u1_struct_0(X0) = u1_struct_0(X1) )
   => ( ~ m1_setfam_1(sK3,u1_struct_0(sK1))
      & m1_setfam_1(sK2,u1_struct_0(sK0))
      & sK2 = sK3
      & u1_struct_0(sK1) = u1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_setfam_1(X3,u1_struct_0(X1))
      & m1_setfam_1(X2,u1_struct_0(X0))
      & X2 = X3
      & u1_struct_0(X0) = u1_struct_0(X1) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_setfam_1(X3,u1_struct_0(X1))
      & m1_setfam_1(X2,u1_struct_0(X0))
      & X2 = X3
      & u1_struct_0(X0) = u1_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_setfam_1(X2,u1_struct_0(X0))
          & X2 = X3
          & u1_struct_0(X0) = u1_struct_0(X1) )
       => m1_setfam_1(X3,u1_struct_0(X1)) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,plain,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2,X3] :
                ( ( m1_setfam_1(X2,u1_struct_0(X0))
                  & X2 = X3
                  & u1_struct_0(X0) = u1_struct_0(X1) )
               => m1_setfam_1(X3,u1_struct_0(X1)) ) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                   => ( ( m1_setfam_1(X2,u1_struct_0(X0))
                        & X2 = X3
                        & u1_struct_0(X0) = u1_struct_0(X1) )
                     => m1_setfam_1(X3,u1_struct_0(X1)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                 => ( ( m1_setfam_1(X2,u1_struct_0(X0))
                      & X2 = X3
                      & u1_struct_0(X0) = u1_struct_0(X1) )
                   => m1_setfam_1(X3,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_waybel_9)).

fof(f14,plain,(
    ~ m1_setfam_1(sK2,u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f13,f9])).

fof(f9,plain,(
    u1_struct_0(sK1) = u1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f13,plain,(
    ~ m1_setfam_1(sK2,u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f12,f10])).

fof(f10,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f8])).

fof(f12,plain,(
    ~ m1_setfam_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:24:35 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (23795)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.49  % (23795)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (23788)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f14,f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    m1_setfam_1(sK2,u1_struct_0(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ~m1_setfam_1(sK3,u1_struct_0(sK1)) & m1_setfam_1(sK2,u1_struct_0(sK0)) & sK2 = sK3 & u1_struct_0(sK1) = u1_struct_0(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f6,f7])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (~m1_setfam_1(X3,u1_struct_0(X1)) & m1_setfam_1(X2,u1_struct_0(X0)) & X2 = X3 & u1_struct_0(X0) = u1_struct_0(X1)) => (~m1_setfam_1(sK3,u1_struct_0(sK1)) & m1_setfam_1(sK2,u1_struct_0(sK0)) & sK2 = sK3 & u1_struct_0(sK1) = u1_struct_0(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f6,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (~m1_setfam_1(X3,u1_struct_0(X1)) & m1_setfam_1(X2,u1_struct_0(X0)) & X2 = X3 & u1_struct_0(X0) = u1_struct_0(X1))),
% 0.21/0.49    inference(flattening,[],[f5])).
% 0.21/0.49  fof(f5,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (~m1_setfam_1(X3,u1_struct_0(X1)) & (m1_setfam_1(X2,u1_struct_0(X0)) & X2 = X3 & u1_struct_0(X0) = u1_struct_0(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,plain,(
% 0.21/0.49    ~! [X0,X1,X2,X3] : ((m1_setfam_1(X2,u1_struct_0(X0)) & X2 = X3 & u1_struct_0(X0) = u1_struct_0(X1)) => m1_setfam_1(X3,u1_struct_0(X1)))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f3])).
% 0.21/0.49  fof(f3,plain,(
% 0.21/0.49    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2,X3] : ((m1_setfam_1(X2,u1_struct_0(X0)) & X2 = X3 & u1_struct_0(X0) = u1_struct_0(X1)) => m1_setfam_1(X3,u1_struct_0(X1)))))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f2])).
% 0.21/0.49  fof(f2,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => ((m1_setfam_1(X2,u1_struct_0(X0)) & X2 = X3 & u1_struct_0(X0) = u1_struct_0(X1)) => m1_setfam_1(X3,u1_struct_0(X1)))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f1])).
% 0.21/0.49  fof(f1,conjecture,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => ((m1_setfam_1(X2,u1_struct_0(X0)) & X2 = X3 & u1_struct_0(X0) = u1_struct_0(X1)) => m1_setfam_1(X3,u1_struct_0(X1)))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_waybel_9)).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ~m1_setfam_1(sK2,u1_struct_0(sK0))),
% 0.21/0.49    inference(backward_demodulation,[],[f13,f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    u1_struct_0(sK1) = u1_struct_0(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ~m1_setfam_1(sK2,u1_struct_0(sK1))),
% 0.21/0.49    inference(backward_demodulation,[],[f12,f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    sK2 = sK3),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ~m1_setfam_1(sK3,u1_struct_0(sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (23795)------------------------------
% 0.21/0.49  % (23795)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (23795)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (23795)Memory used [KB]: 6140
% 0.21/0.49  % (23795)Time elapsed: 0.004 s
% 0.21/0.49  % (23795)------------------------------
% 0.21/0.49  % (23795)------------------------------
% 0.21/0.49  % (23787)Success in time 0.137 s
%------------------------------------------------------------------------------
