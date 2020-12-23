%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:29 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :   35 (  47 expanded)
%              Number of leaves         :    8 (  12 expanded)
%              Depth                    :   10
%              Number of atoms          :  125 ( 167 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    9 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f68,plain,(
    $false ),
    inference(subsumption_resolution,[],[f67,f22])).

fof(f22,plain,(
    r1_tarski(k3_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_tarski(sK2,sK1)
    & r2_hidden(sK2,sK0)
    & r1_tarski(k3_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X2,X1)
        & r2_hidden(X2,X0)
        & r1_tarski(k3_tarski(X0),X1) )
   => ( ~ r1_tarski(sK2,sK1)
      & r2_hidden(sK2,sK0)
      & r1_tarski(k3_tarski(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X2,X1)
      & r2_hidden(X2,X0)
      & r1_tarski(k3_tarski(X0),X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X2,X1)
      & r2_hidden(X2,X0)
      & r1_tarski(k3_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(X2,X0)
          & r1_tarski(k3_tarski(X0),X1) )
       => r1_tarski(X2,X1) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X0)
        & r1_tarski(k3_tarski(X0),X1) )
     => r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).

fof(f67,plain,(
    ~ r1_tarski(k3_tarski(sK0),sK1) ),
    inference(resolution,[],[f62,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,X0)
      | ~ r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f32,f24])).

fof(f24,plain,(
    ~ r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f62,plain,(
    r1_tarski(sK2,k3_tarski(sK0)) ),
    inference(resolution,[],[f58,f23])).

fof(f23,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(resolution,[],[f41,f33])).

fof(f33,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(resolution,[],[f29,f35])).

fof(f35,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:02:56 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.37  ipcrm: permission denied for id (1209401344)
% 0.15/0.38  ipcrm: permission denied for id (1212678145)
% 0.15/0.38  ipcrm: permission denied for id (1209434114)
% 0.15/0.38  ipcrm: permission denied for id (1209466883)
% 0.15/0.38  ipcrm: permission denied for id (1209532422)
% 0.15/0.38  ipcrm: permission denied for id (1209565191)
% 0.15/0.38  ipcrm: permission denied for id (1215299592)
% 0.15/0.39  ipcrm: permission denied for id (1215365130)
% 0.15/0.39  ipcrm: permission denied for id (1209663499)
% 0.15/0.39  ipcrm: permission denied for id (1215430669)
% 0.15/0.39  ipcrm: permission denied for id (1212973070)
% 0.15/0.39  ipcrm: permission denied for id (1209761807)
% 0.15/0.39  ipcrm: permission denied for id (1213005840)
% 0.15/0.40  ipcrm: permission denied for id (1215463441)
% 0.15/0.40  ipcrm: permission denied for id (1209892882)
% 0.15/0.40  ipcrm: permission denied for id (1209925651)
% 0.15/0.40  ipcrm: permission denied for id (1213071380)
% 0.15/0.40  ipcrm: permission denied for id (1215496213)
% 0.15/0.40  ipcrm: permission denied for id (1215561751)
% 0.15/0.40  ipcrm: permission denied for id (1213202456)
% 0.15/0.41  ipcrm: permission denied for id (1213235225)
% 0.15/0.41  ipcrm: permission denied for id (1210089500)
% 0.15/0.41  ipcrm: permission denied for id (1213366302)
% 0.15/0.41  ipcrm: permission denied for id (1213399071)
% 0.15/0.41  ipcrm: permission denied for id (1210155040)
% 0.15/0.42  ipcrm: permission denied for id (1213464610)
% 0.23/0.42  ipcrm: permission denied for id (1210220579)
% 0.23/0.42  ipcrm: permission denied for id (1210253348)
% 0.23/0.42  ipcrm: permission denied for id (1215725605)
% 0.23/0.42  ipcrm: permission denied for id (1210286118)
% 0.23/0.42  ipcrm: permission denied for id (1213530151)
% 0.23/0.42  ipcrm: permission denied for id (1213562920)
% 0.23/0.42  ipcrm: permission denied for id (1213595689)
% 0.23/0.43  ipcrm: permission denied for id (1213628458)
% 0.23/0.43  ipcrm: permission denied for id (1210417195)
% 0.23/0.43  ipcrm: permission denied for id (1213661228)
% 0.23/0.43  ipcrm: permission denied for id (1215758381)
% 0.23/0.43  ipcrm: permission denied for id (1210515502)
% 0.23/0.43  ipcrm: permission denied for id (1210548271)
% 0.23/0.44  ipcrm: permission denied for id (1213792306)
% 0.23/0.44  ipcrm: permission denied for id (1210679347)
% 0.23/0.44  ipcrm: permission denied for id (1213825076)
% 0.23/0.44  ipcrm: permission denied for id (1210744885)
% 0.23/0.44  ipcrm: permission denied for id (1210777654)
% 0.23/0.44  ipcrm: permission denied for id (1210810423)
% 0.23/0.44  ipcrm: permission denied for id (1210843192)
% 0.23/0.45  ipcrm: permission denied for id (1213857849)
% 0.23/0.45  ipcrm: permission denied for id (1215856698)
% 0.23/0.45  ipcrm: permission denied for id (1215922235)
% 0.23/0.45  ipcrm: permission denied for id (1215987773)
% 0.23/0.45  ipcrm: permission denied for id (1211072575)
% 0.23/0.45  ipcrm: permission denied for id (1214087232)
% 0.23/0.46  ipcrm: permission denied for id (1211138113)
% 0.23/0.46  ipcrm: permission denied for id (1211170882)
% 0.23/0.46  ipcrm: permission denied for id (1216086083)
% 0.23/0.46  ipcrm: permission denied for id (1211269188)
% 0.23/0.46  ipcrm: permission denied for id (1214185541)
% 0.23/0.46  ipcrm: permission denied for id (1211301958)
% 0.23/0.46  ipcrm: permission denied for id (1211334727)
% 0.23/0.46  ipcrm: permission denied for id (1211367496)
% 0.23/0.47  ipcrm: permission denied for id (1214218313)
% 0.23/0.47  ipcrm: permission denied for id (1214251082)
% 0.23/0.47  ipcrm: permission denied for id (1211465803)
% 0.23/0.47  ipcrm: permission denied for id (1211498572)
% 0.23/0.47  ipcrm: permission denied for id (1211531341)
% 0.23/0.47  ipcrm: permission denied for id (1211564110)
% 0.23/0.47  ipcrm: permission denied for id (1211596879)
% 0.23/0.48  ipcrm: permission denied for id (1211629648)
% 0.23/0.48  ipcrm: permission denied for id (1211662417)
% 0.23/0.48  ipcrm: permission denied for id (1214283858)
% 0.23/0.48  ipcrm: permission denied for id (1211695187)
% 0.23/0.48  ipcrm: permission denied for id (1211727956)
% 0.23/0.48  ipcrm: permission denied for id (1211760726)
% 0.23/0.48  ipcrm: permission denied for id (1216151639)
% 0.23/0.49  ipcrm: permission denied for id (1211826264)
% 0.23/0.49  ipcrm: permission denied for id (1214382169)
% 0.23/0.49  ipcrm: permission denied for id (1211859034)
% 0.23/0.49  ipcrm: permission denied for id (1214414939)
% 0.23/0.49  ipcrm: permission denied for id (1211891804)
% 0.23/0.49  ipcrm: permission denied for id (1211957342)
% 0.23/0.50  ipcrm: permission denied for id (1214513248)
% 0.23/0.50  ipcrm: permission denied for id (1214546017)
% 0.23/0.50  ipcrm: permission denied for id (1216249954)
% 0.23/0.50  ipcrm: permission denied for id (1216282723)
% 0.23/0.50  ipcrm: permission denied for id (1216315492)
% 0.23/0.50  ipcrm: permission denied for id (1214677093)
% 0.23/0.50  ipcrm: permission denied for id (1214709862)
% 0.23/0.50  ipcrm: permission denied for id (1216381031)
% 0.23/0.50  ipcrm: permission denied for id (1214775400)
% 0.23/0.51  ipcrm: permission denied for id (1214808169)
% 0.23/0.51  ipcrm: permission denied for id (1212088426)
% 0.23/0.51  ipcrm: permission denied for id (1212121195)
% 0.23/0.51  ipcrm: permission denied for id (1212153964)
% 0.23/0.51  ipcrm: permission denied for id (1214840941)
% 0.23/0.51  ipcrm: permission denied for id (1214873710)
% 0.23/0.51  ipcrm: permission denied for id (1212219503)
% 0.23/0.52  ipcrm: permission denied for id (1215004785)
% 0.23/0.52  ipcrm: permission denied for id (1212317810)
% 0.23/0.52  ipcrm: permission denied for id (1212350579)
% 0.23/0.52  ipcrm: permission denied for id (1216446580)
% 0.23/0.52  ipcrm: permission denied for id (1215037557)
% 0.23/0.52  ipcrm: permission denied for id (1212416118)
% 0.23/0.52  ipcrm: permission denied for id (1212448887)
% 0.23/0.52  ipcrm: permission denied for id (1215070328)
% 0.23/0.53  ipcrm: permission denied for id (1212514426)
% 0.23/0.53  ipcrm: permission denied for id (1212547195)
% 0.23/0.53  ipcrm: permission denied for id (1216512124)
% 0.23/0.53  ipcrm: permission denied for id (1215168637)
% 0.23/0.53  ipcrm: permission denied for id (1212612734)
% 0.23/0.53  ipcrm: permission denied for id (1215201407)
% 0.80/0.67  % (30015)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.20/0.67  % (30006)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.20/0.67  % (30006)Refutation found. Thanks to Tanya!
% 1.20/0.67  % SZS status Theorem for theBenchmark
% 1.20/0.67  % (30023)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.20/0.67  % SZS output start Proof for theBenchmark
% 1.20/0.67  fof(f68,plain,(
% 1.20/0.67    $false),
% 1.20/0.67    inference(subsumption_resolution,[],[f67,f22])).
% 1.20/0.67  fof(f22,plain,(
% 1.20/0.67    r1_tarski(k3_tarski(sK0),sK1)),
% 1.20/0.67    inference(cnf_transformation,[],[f13])).
% 1.20/0.67  fof(f13,plain,(
% 1.20/0.67    ~r1_tarski(sK2,sK1) & r2_hidden(sK2,sK0) & r1_tarski(k3_tarski(sK0),sK1)),
% 1.20/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f12])).
% 1.20/0.67  fof(f12,plain,(
% 1.20/0.67    ? [X0,X1,X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0) & r1_tarski(k3_tarski(X0),X1)) => (~r1_tarski(sK2,sK1) & r2_hidden(sK2,sK0) & r1_tarski(k3_tarski(sK0),sK1))),
% 1.20/0.67    introduced(choice_axiom,[])).
% 1.20/0.67  fof(f8,plain,(
% 1.20/0.67    ? [X0,X1,X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0) & r1_tarski(k3_tarski(X0),X1))),
% 1.20/0.67    inference(flattening,[],[f7])).
% 1.20/0.67  fof(f7,plain,(
% 1.20/0.67    ? [X0,X1,X2] : (~r1_tarski(X2,X1) & (r2_hidden(X2,X0) & r1_tarski(k3_tarski(X0),X1)))),
% 1.20/0.67    inference(ennf_transformation,[],[f6])).
% 1.20/0.67  fof(f6,negated_conjecture,(
% 1.20/0.67    ~! [X0,X1,X2] : ((r2_hidden(X2,X0) & r1_tarski(k3_tarski(X0),X1)) => r1_tarski(X2,X1))),
% 1.20/0.67    inference(negated_conjecture,[],[f5])).
% 1.20/0.67  fof(f5,conjecture,(
% 1.20/0.67    ! [X0,X1,X2] : ((r2_hidden(X2,X0) & r1_tarski(k3_tarski(X0),X1)) => r1_tarski(X2,X1))),
% 1.20/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).
% 1.20/0.67  fof(f67,plain,(
% 1.20/0.67    ~r1_tarski(k3_tarski(sK0),sK1)),
% 1.20/0.67    inference(resolution,[],[f62,f43])).
% 1.20/0.67  fof(f43,plain,(
% 1.20/0.67    ( ! [X0] : (~r1_tarski(sK2,X0) | ~r1_tarski(X0,sK1)) )),
% 1.20/0.67    inference(resolution,[],[f32,f24])).
% 1.20/0.67  fof(f24,plain,(
% 1.20/0.67    ~r1_tarski(sK2,sK1)),
% 1.20/0.67    inference(cnf_transformation,[],[f13])).
% 1.20/0.67  fof(f32,plain,(
% 1.20/0.67    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.20/0.67    inference(cnf_transformation,[],[f11])).
% 1.20/0.67  fof(f11,plain,(
% 1.20/0.67    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.20/0.67    inference(flattening,[],[f10])).
% 1.20/0.67  fof(f10,plain,(
% 1.20/0.67    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.20/0.67    inference(ennf_transformation,[],[f2])).
% 1.20/0.67  fof(f2,axiom,(
% 1.20/0.67    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.20/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.20/0.67  fof(f62,plain,(
% 1.20/0.67    r1_tarski(sK2,k3_tarski(sK0))),
% 1.20/0.67    inference(resolution,[],[f58,f23])).
% 1.20/0.67  fof(f23,plain,(
% 1.20/0.67    r2_hidden(sK2,sK0)),
% 1.20/0.67    inference(cnf_transformation,[],[f13])).
% 1.20/0.67  fof(f58,plain,(
% 1.20/0.67    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1))) )),
% 1.20/0.67    inference(resolution,[],[f41,f33])).
% 1.20/0.67  fof(f33,plain,(
% 1.20/0.67    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))) )),
% 1.20/0.67    inference(cnf_transformation,[],[f4])).
% 1.20/0.67  fof(f4,axiom,(
% 1.20/0.67    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 1.20/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).
% 1.20/0.67  fof(f41,plain,(
% 1.20/0.67    ( ! [X2,X0,X1] : (~r1_tarski(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | r1_tarski(X0,X2)) )),
% 1.20/0.67    inference(resolution,[],[f29,f35])).
% 1.20/0.67  fof(f35,plain,(
% 1.20/0.67    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 1.20/0.67    inference(equality_resolution,[],[f25])).
% 1.20/0.67  fof(f25,plain,(
% 1.20/0.67    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.20/0.67    inference(cnf_transformation,[],[f17])).
% 1.20/0.67  fof(f17,plain,(
% 1.20/0.67    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.20/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).
% 1.20/0.67  fof(f16,plain,(
% 1.20/0.67    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 1.20/0.67    introduced(choice_axiom,[])).
% 1.20/0.67  fof(f15,plain,(
% 1.20/0.67    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.20/0.67    inference(rectify,[],[f14])).
% 1.20/0.67  fof(f14,plain,(
% 1.20/0.67    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.20/0.67    inference(nnf_transformation,[],[f3])).
% 1.20/0.67  fof(f3,axiom,(
% 1.20/0.67    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.20/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.20/0.67  fof(f29,plain,(
% 1.20/0.67    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.20/0.67    inference(cnf_transformation,[],[f21])).
% 1.20/0.67  fof(f21,plain,(
% 1.20/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.20/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).
% 1.20/0.67  fof(f20,plain,(
% 1.20/0.67    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.20/0.67    introduced(choice_axiom,[])).
% 1.20/0.67  fof(f19,plain,(
% 1.20/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.20/0.67    inference(rectify,[],[f18])).
% 1.20/0.67  fof(f18,plain,(
% 1.20/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.20/0.67    inference(nnf_transformation,[],[f9])).
% 1.20/0.67  fof(f9,plain,(
% 1.20/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.20/0.67    inference(ennf_transformation,[],[f1])).
% 1.20/0.67  fof(f1,axiom,(
% 1.20/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.20/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.20/0.67  % SZS output end Proof for theBenchmark
% 1.20/0.67  % (30006)------------------------------
% 1.20/0.67  % (30006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.67  % (30006)Termination reason: Refutation
% 1.20/0.67  
% 1.20/0.67  % (30006)Memory used [KB]: 6268
% 1.20/0.67  % (30006)Time elapsed: 0.100 s
% 1.20/0.67  % (30006)------------------------------
% 1.20/0.67  % (30006)------------------------------
% 1.20/0.67  % (29823)Success in time 0.305 s
%------------------------------------------------------------------------------
