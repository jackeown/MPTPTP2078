%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t136_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:00 EDT 2019

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :  106 (1713 expanded)
%              Number of leaves         :    4 ( 288 expanded)
%              Depth                    :   25
%              Number of atoms          :  422 (11521 expanded)
%              Number of equality atoms :    2 (  52 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3355,plain,(
    $false ),
    inference(resolution,[],[f3334,f44])).

fof(f44,plain,(
    ! [X0] : r2_hidden(X0,sK5(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | r2_tarski(X2,X1)
          | ~ r1_tarski(X2,X1) )
      & ! [X3] :
          ( ? [X4] :
              ( ! [X5] :
                  ( r2_hidden(X5,X4)
                  | ~ r1_tarski(X5,X3) )
              & r2_hidden(X4,X1) )
          | ~ r2_hidden(X3,X1) )
      & ! [X6,X7] :
          ( r2_hidden(X7,X1)
          | ~ r1_tarski(X7,X6)
          | ~ r2_hidden(X6,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | r2_tarski(X2,X1)
          | ~ r1_tarski(X2,X1) )
      & ! [X3] :
          ( ? [X4] :
              ( ! [X5] :
                  ( r2_hidden(X5,X4)
                  | ~ r1_tarski(X5,X3) )
              & r2_hidden(X4,X1) )
          | ~ r2_hidden(X3,X1) )
      & ! [X6,X7] :
          ( r2_hidden(X7,X1)
          | ~ r1_tarski(X7,X6)
          | ~ r2_hidden(X6,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & ~ r2_tarski(X2,X1)
            & r1_tarski(X2,X1) )
      & ! [X3] :
          ~ ( ! [X4] :
                ~ ( ! [X5] :
                      ( r1_tarski(X5,X3)
                     => r2_hidden(X5,X4) )
                  & r2_hidden(X4,X1) )
            & r2_hidden(X3,X1) )
      & ! [X6,X7] :
          ( ( r1_tarski(X7,X6)
            & r2_hidden(X6,X1) )
         => r2_hidden(X7,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(rectify,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & ~ r2_tarski(X2,X1)
            & r1_tarski(X2,X1) )
      & ! [X2] :
          ~ ( ! [X3] :
                ~ ( ! [X4] :
                      ( r1_tarski(X4,X2)
                     => r2_hidden(X4,X3) )
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X1) )
      & ! [X2,X3] :
          ( ( r1_tarski(X3,X2)
            & r2_hidden(X2,X1) )
         => r2_hidden(X3,X1) )
      & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t136_zfmisc_1.p',t9_tarski)).

fof(f3334,plain,(
    ! [X1] : ~ r2_hidden(sK0,sK5(X1)) ),
    inference(subsumption_resolution,[],[f3333,f1817])).

fof(f1817,plain,(
    ! [X11] :
      ( r2_hidden(sK3(sK5(X11)),sK5(X11))
      | ~ r2_hidden(sK0,sK5(X11)) ) ),
    inference(subsumption_resolution,[],[f1804,f105])).

fof(f105,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK5(X0)),sK5(X0))
      | ~ r2_hidden(sK2(sK5(X0)),sK5(X0))
      | ~ r2_hidden(sK0,sK5(X0)) ) ),
    inference(subsumption_resolution,[],[f104,f37])).

fof(f37,plain,(
    ! [X1] :
      ( r1_tarski(sK4(X1),X1)
      | ~ r2_hidden(sK2(X1),X1)
      | r2_hidden(sK3(X1),X1)
      | ~ r2_hidden(sK0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
    ! [X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & ~ r2_tarski(X2,X1)
          & r1_tarski(X2,X1) )
      | ? [X3] :
          ( ~ r2_hidden(k1_zfmisc_1(X3),X1)
          & r2_hidden(X3,X1) )
      | ? [X4,X5] :
          ( ~ r2_hidden(X5,X1)
          & r1_tarski(X5,X4)
          & r2_hidden(X4,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
    ! [X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & ~ r2_tarski(X2,X1)
          & r1_tarski(X2,X1) )
      | ? [X3] :
          ( ~ r2_hidden(k1_zfmisc_1(X3),X1)
          & r2_hidden(X3,X1) )
      | ? [X4,X5] :
          ( ~ r2_hidden(X5,X1)
          & r1_tarski(X5,X4)
          & r2_hidden(X4,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ~ ! [X0] :
      ? [X1] :
        ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X1)
              & ~ r2_tarski(X2,X1)
              & r1_tarski(X2,X1) )
        & ! [X3] :
            ( r2_hidden(X3,X1)
           => r2_hidden(k1_zfmisc_1(X3),X1) )
        & ! [X4,X5] :
            ( ( r1_tarski(X5,X4)
              & r2_hidden(X4,X1) )
           => r2_hidden(X5,X1) )
        & r2_hidden(X0,X1) ) ),
    inference(rectify,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
      ? [X1] :
        ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X1)
              & ~ r2_tarski(X2,X1)
              & r1_tarski(X2,X1) )
        & ! [X2] :
            ( r2_hidden(X2,X1)
           => r2_hidden(k1_zfmisc_1(X2),X1) )
        & ! [X2,X3] :
            ( ( r1_tarski(X3,X2)
              & r2_hidden(X2,X1) )
           => r2_hidden(X3,X1) )
        & r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & ~ r2_tarski(X2,X1)
            & r1_tarski(X2,X1) )
      & ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(k1_zfmisc_1(X2),X1) )
      & ! [X2,X3] :
          ( ( r1_tarski(X3,X2)
            & r2_hidden(X2,X1) )
         => r2_hidden(X3,X1) )
      & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t136_zfmisc_1.p',t136_zfmisc_1)).

fof(f104,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK4(sK5(X0)),sK5(X0))
      | ~ r2_hidden(sK2(sK5(X0)),sK5(X0))
      | r2_hidden(sK3(sK5(X0)),sK5(X0))
      | ~ r2_hidden(sK0,sK5(X0)) ) ),
    inference(subsumption_resolution,[],[f102,f39])).

fof(f39,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4(X1),X1)
      | ~ r2_hidden(sK2(X1),X1)
      | r2_hidden(sK3(X1),X1)
      | ~ r2_hidden(sK0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f102,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK4(sK5(X0)),sK5(X0))
      | r2_hidden(sK4(sK5(X0)),sK5(X0))
      | ~ r2_hidden(sK2(sK5(X0)),sK5(X0))
      | r2_hidden(sK3(sK5(X0)),sK5(X0))
      | ~ r2_hidden(sK0,sK5(X0)) ) ),
    inference(resolution,[],[f42,f38])).

fof(f38,plain,(
    ! [X1] :
      ( ~ r2_tarski(sK4(X1),X1)
      | ~ r2_hidden(sK2(X1),X1)
      | r2_hidden(sK3(X1),X1)
      | ~ r2_hidden(sK0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X2,X0] :
      ( r2_tarski(X2,sK5(X0))
      | ~ r1_tarski(X2,sK5(X0))
      | r2_hidden(X2,sK5(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1804,plain,(
    ! [X11] :
      ( ~ r2_hidden(sK0,sK5(X11))
      | r2_hidden(sK2(sK5(X11)),sK5(X11))
      | r2_hidden(sK3(sK5(X11)),sK5(X11)) ) ),
    inference(duplicate_literal_removal,[],[f1770])).

fof(f1770,plain,(
    ! [X11] :
      ( ~ r2_hidden(sK0,sK5(X11))
      | r2_hidden(sK2(sK5(X11)),sK5(X11))
      | ~ r2_hidden(sK0,sK5(X11))
      | r2_hidden(sK3(sK5(X11)),sK5(X11)) ) ),
    inference(resolution,[],[f1701,f1160])).

fof(f1160,plain,(
    ! [X0] :
      ( r1_tarski(sK2(sK5(X0)),sK1(sK5(X0)))
      | ~ r2_hidden(sK0,sK5(X0))
      | r2_hidden(sK3(sK5(X0)),sK5(X0)) ) ),
    inference(duplicate_literal_removal,[],[f1157])).

fof(f1157,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK5(X0)),sK5(X0))
      | ~ r2_hidden(sK0,sK5(X0))
      | r1_tarski(sK2(sK5(X0)),sK1(sK5(X0)))
      | r1_tarski(sK2(sK5(X0)),sK1(sK5(X0))) ) ),
    inference(resolution,[],[f323,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK8(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t136_zfmisc_1.p',d3_tarski)).

fof(f323,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK8(sK2(sK5(X2)),X3),sK1(sK5(X2)))
      | r2_hidden(sK3(sK5(X2)),sK5(X2))
      | ~ r2_hidden(sK0,sK5(X2))
      | r1_tarski(sK2(sK5(X2)),X3) ) ),
    inference(resolution,[],[f132,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f132,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK2(sK5(X1)))
      | ~ r2_hidden(sK0,sK5(X1))
      | r2_hidden(sK3(sK5(X1)),sK5(X1))
      | r2_hidden(X0,sK1(sK5(X1))) ) ),
    inference(subsumption_resolution,[],[f131,f81])).

fof(f81,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(sK4(X11),X11)
      | ~ r2_hidden(X10,sK2(X11))
      | ~ r2_hidden(sK0,X11)
      | r2_hidden(sK3(X11),X11)
      | r2_hidden(X10,sK1(X11)) ) ),
    inference(resolution,[],[f49,f33])).

fof(f33,plain,(
    ! [X1] :
      ( r1_tarski(sK2(X1),sK1(X1))
      | ~ r2_hidden(sK0,X1)
      | r2_hidden(sK3(X1),X1)
      | ~ r2_hidden(sK4(X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK2(sK5(X1)))
      | ~ r2_hidden(sK0,sK5(X1))
      | r2_hidden(sK3(sK5(X1)),sK5(X1))
      | r2_hidden(X0,sK1(sK5(X1)))
      | r2_hidden(sK4(sK5(X1)),sK5(X1)) ) ),
    inference(subsumption_resolution,[],[f130,f83])).

fof(f83,plain,(
    ! [X14,X15] :
      ( ~ r2_hidden(X14,sK2(X15))
      | r2_hidden(X14,sK1(X15))
      | ~ r2_hidden(sK0,X15)
      | r2_hidden(sK3(X15),X15)
      | r1_tarski(sK4(X15),X15) ) ),
    inference(resolution,[],[f49,f31])).

fof(f31,plain,(
    ! [X1] :
      ( r1_tarski(sK2(X1),sK1(X1))
      | ~ r2_hidden(sK0,X1)
      | r2_hidden(sK3(X1),X1)
      | r1_tarski(sK4(X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK2(sK5(X1)))
      | ~ r2_hidden(sK0,sK5(X1))
      | r2_hidden(sK3(sK5(X1)),sK5(X1))
      | r2_hidden(X0,sK1(sK5(X1)))
      | ~ r1_tarski(sK4(sK5(X1)),sK5(X1))
      | r2_hidden(sK4(sK5(X1)),sK5(X1)) ) ),
    inference(resolution,[],[f82,f42])).

fof(f82,plain,(
    ! [X12,X13] :
      ( ~ r2_tarski(sK4(X13),X13)
      | ~ r2_hidden(X12,sK2(X13))
      | ~ r2_hidden(sK0,X13)
      | r2_hidden(sK3(X13),X13)
      | r2_hidden(X12,sK1(X13)) ) ),
    inference(resolution,[],[f49,f32])).

fof(f32,plain,(
    ! [X1] :
      ( r1_tarski(sK2(X1),sK1(X1))
      | ~ r2_hidden(sK0,X1)
      | r2_hidden(sK3(X1),X1)
      | ~ r2_tarski(sK4(X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1701,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK1(sK5(X0)))
      | ~ r2_hidden(sK0,sK5(X0))
      | r2_hidden(X1,sK5(X0)) ) ),
    inference(resolution,[],[f1696,f43])).

fof(f43,plain,(
    ! [X6,X0,X7] :
      ( ~ r2_hidden(X6,sK5(X0))
      | ~ r1_tarski(X7,X6)
      | r2_hidden(X7,sK5(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1696,plain,(
    ! [X0] :
      ( r2_hidden(sK1(sK5(X0)),sK5(X0))
      | ~ r2_hidden(sK0,sK5(X0)) ) ),
    inference(subsumption_resolution,[],[f1695,f1629])).

fof(f1629,plain,(
    ! [X5] :
      ( ~ r2_hidden(sK4(sK5(X5)),sK5(X5))
      | ~ r2_hidden(sK0,sK5(X5))
      | r2_hidden(sK1(sK5(X5)),sK5(X5)) ) ),
    inference(subsumption_resolution,[],[f1614,f107])).

fof(f107,plain,(
    ! [X1] :
      ( r2_hidden(sK3(sK5(X1)),sK5(X1))
      | r2_hidden(sK1(sK5(X1)),sK5(X1))
      | ~ r2_hidden(sK0,sK5(X1)) ) ),
    inference(subsumption_resolution,[],[f106,f25])).

fof(f25,plain,(
    ! [X1] :
      ( r1_tarski(sK4(X1),X1)
      | r2_hidden(sK1(X1),X1)
      | r2_hidden(sK3(X1),X1)
      | ~ r2_hidden(sK0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f106,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK4(sK5(X1)),sK5(X1))
      | r2_hidden(sK1(sK5(X1)),sK5(X1))
      | r2_hidden(sK3(sK5(X1)),sK5(X1))
      | ~ r2_hidden(sK0,sK5(X1)) ) ),
    inference(subsumption_resolution,[],[f103,f27])).

fof(f27,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4(X1),X1)
      | r2_hidden(sK1(X1),X1)
      | r2_hidden(sK3(X1),X1)
      | ~ r2_hidden(sK0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f103,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK4(sK5(X1)),sK5(X1))
      | r2_hidden(sK4(sK5(X1)),sK5(X1))
      | r2_hidden(sK1(sK5(X1)),sK5(X1))
      | r2_hidden(sK3(sK5(X1)),sK5(X1))
      | ~ r2_hidden(sK0,sK5(X1)) ) ),
    inference(resolution,[],[f42,f26])).

fof(f26,plain,(
    ! [X1] :
      ( ~ r2_tarski(sK4(X1),X1)
      | r2_hidden(sK1(X1),X1)
      | r2_hidden(sK3(X1),X1)
      | ~ r2_hidden(sK0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1614,plain,(
    ! [X5] :
      ( ~ r2_hidden(sK3(sK5(X5)),sK5(X5))
      | r2_hidden(sK1(sK5(X5)),sK5(X5))
      | ~ r2_hidden(sK0,sK5(X5))
      | ~ r2_hidden(sK4(sK5(X5)),sK5(X5)) ) ),
    inference(resolution,[],[f538,f24])).

fof(f24,plain,(
    ! [X1] :
      ( ~ r2_hidden(k1_zfmisc_1(sK3(X1)),X1)
      | r2_hidden(sK1(X1),X1)
      | ~ r2_hidden(sK0,X1)
      | ~ r2_hidden(sK4(X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f538,plain,(
    ! [X4,X5] :
      ( r2_hidden(k1_zfmisc_1(X4),sK5(X5))
      | ~ r2_hidden(X4,sK5(X5)) ) ),
    inference(duplicate_literal_removal,[],[f534])).

fof(f534,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,sK5(X5))
      | r2_hidden(k1_zfmisc_1(X4),sK5(X5))
      | ~ r2_hidden(X4,sK5(X5)) ) ),
    inference(resolution,[],[f291,f89])).

fof(f89,plain,(
    ! [X6,X7,X5] :
      ( ~ r1_tarski(X5,sK6(X6,X7))
      | r2_hidden(X5,sK5(X6))
      | ~ r2_hidden(X7,sK5(X6)) ) ),
    inference(resolution,[],[f43,f41])).

fof(f41,plain,(
    ! [X0,X3] :
      ( r2_hidden(sK6(X0,X3),sK5(X0))
      | ~ r2_hidden(X3,sK5(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f291,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),sK6(X1,X0))
      | ~ r2_hidden(X0,sK5(X1)) ) ),
    inference(duplicate_literal_removal,[],[f289])).

fof(f289,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK5(X1))
      | r1_tarski(k1_zfmisc_1(X0),sK6(X1,X0))
      | r1_tarski(k1_zfmisc_1(X0),sK6(X1,X0)) ) ),
    inference(resolution,[],[f101,f71])).

fof(f71,plain,(
    ! [X4,X5] :
      ( r1_tarski(sK8(k1_zfmisc_1(X4),X5),X4)
      | r1_tarski(k1_zfmisc_1(X4),X5) ) ),
    inference(resolution,[],[f50,f54])).

fof(f54,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t136_zfmisc_1.p',d1_zfmisc_1)).

fof(f101,plain,(
    ! [X26,X24,X25] :
      ( ~ r1_tarski(sK8(X24,sK6(X25,X26)),X26)
      | ~ r2_hidden(X26,sK5(X25))
      | r1_tarski(X24,sK6(X25,X26)) ) ),
    inference(resolution,[],[f40,f51])).

fof(f40,plain,(
    ! [X0,X5,X3] :
      ( r2_hidden(X5,sK6(X0,X3))
      | ~ r1_tarski(X5,X3)
      | ~ r2_hidden(X3,sK5(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1695,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,sK5(X0))
      | r2_hidden(sK1(sK5(X0)),sK5(X0))
      | r2_hidden(sK4(sK5(X0)),sK5(X0)) ) ),
    inference(subsumption_resolution,[],[f1694,f1627])).

fof(f1627,plain,(
    ! [X3] :
      ( r1_tarski(sK4(sK5(X3)),sK5(X3))
      | ~ r2_hidden(sK0,sK5(X3))
      | r2_hidden(sK1(sK5(X3)),sK5(X3)) ) ),
    inference(subsumption_resolution,[],[f1612,f107])).

fof(f1612,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK3(sK5(X3)),sK5(X3))
      | r2_hidden(sK1(sK5(X3)),sK5(X3))
      | ~ r2_hidden(sK0,sK5(X3))
      | r1_tarski(sK4(sK5(X3)),sK5(X3)) ) ),
    inference(resolution,[],[f538,f22])).

fof(f22,plain,(
    ! [X1] :
      ( ~ r2_hidden(k1_zfmisc_1(sK3(X1)),X1)
      | r2_hidden(sK1(X1),X1)
      | ~ r2_hidden(sK0,X1)
      | r1_tarski(sK4(X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1694,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,sK5(X0))
      | r2_hidden(sK1(sK5(X0)),sK5(X0))
      | ~ r1_tarski(sK4(sK5(X0)),sK5(X0))
      | r2_hidden(sK4(sK5(X0)),sK5(X0)) ) ),
    inference(resolution,[],[f1628,f42])).

fof(f1628,plain,(
    ! [X4] :
      ( ~ r2_tarski(sK4(sK5(X4)),sK5(X4))
      | ~ r2_hidden(sK0,sK5(X4))
      | r2_hidden(sK1(sK5(X4)),sK5(X4)) ) ),
    inference(subsumption_resolution,[],[f1613,f107])).

fof(f1613,plain,(
    ! [X4] :
      ( ~ r2_hidden(sK3(sK5(X4)),sK5(X4))
      | r2_hidden(sK1(sK5(X4)),sK5(X4))
      | ~ r2_hidden(sK0,sK5(X4))
      | ~ r2_tarski(sK4(sK5(X4)),sK5(X4)) ) ),
    inference(resolution,[],[f538,f23])).

fof(f23,plain,(
    ! [X1] :
      ( ~ r2_hidden(k1_zfmisc_1(sK3(X1)),X1)
      | r2_hidden(sK1(X1),X1)
      | ~ r2_hidden(sK0,X1)
      | ~ r2_tarski(sK4(X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3333,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK0,sK5(X1))
      | ~ r2_hidden(sK3(sK5(X1)),sK5(X1)) ) ),
    inference(subsumption_resolution,[],[f3329,f3242])).

fof(f3242,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK4(sK5(X0)),sK5(X0))
      | ~ r2_hidden(sK0,sK5(X0)) ) ),
    inference(subsumption_resolution,[],[f3241,f2894])).

fof(f2894,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4(sK5(X1)),sK5(X1))
      | ~ r2_hidden(sK0,sK5(X1)) ) ),
    inference(subsumption_resolution,[],[f2891,f1814])).

fof(f1814,plain,(
    ! [X6] :
      ( ~ r2_hidden(sK4(sK5(X6)),sK5(X6))
      | r2_hidden(sK3(sK5(X6)),sK5(X6))
      | ~ r2_hidden(sK0,sK5(X6)) ) ),
    inference(subsumption_resolution,[],[f1807,f1632])).

fof(f1632,plain,(
    ! [X8] :
      ( ~ r2_hidden(sK4(sK5(X8)),sK5(X8))
      | ~ r2_hidden(sK0,sK5(X8))
      | ~ r2_hidden(sK2(sK5(X8)),sK5(X8)) ) ),
    inference(subsumption_resolution,[],[f1617,f39])).

fof(f1617,plain,(
    ! [X8] :
      ( ~ r2_hidden(sK3(sK5(X8)),sK5(X8))
      | ~ r2_hidden(sK2(sK5(X8)),sK5(X8))
      | ~ r2_hidden(sK0,sK5(X8))
      | ~ r2_hidden(sK4(sK5(X8)),sK5(X8)) ) ),
    inference(resolution,[],[f538,f36])).

fof(f36,plain,(
    ! [X1] :
      ( ~ r2_hidden(k1_zfmisc_1(sK3(X1)),X1)
      | ~ r2_hidden(sK2(X1),X1)
      | ~ r2_hidden(sK0,X1)
      | ~ r2_hidden(sK4(X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1807,plain,(
    ! [X6] :
      ( ~ r2_hidden(sK0,sK5(X6))
      | r2_hidden(sK2(sK5(X6)),sK5(X6))
      | r2_hidden(sK3(sK5(X6)),sK5(X6))
      | ~ r2_hidden(sK4(sK5(X6)),sK5(X6)) ) ),
    inference(duplicate_literal_removal,[],[f1766])).

fof(f1766,plain,(
    ! [X6] :
      ( ~ r2_hidden(sK0,sK5(X6))
      | r2_hidden(sK2(sK5(X6)),sK5(X6))
      | ~ r2_hidden(sK0,sK5(X6))
      | r2_hidden(sK3(sK5(X6)),sK5(X6))
      | ~ r2_hidden(sK4(sK5(X6)),sK5(X6)) ) ),
    inference(resolution,[],[f1701,f33])).

fof(f2891,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK0,sK5(X1))
      | ~ r2_hidden(sK4(sK5(X1)),sK5(X1))
      | ~ r2_hidden(sK3(sK5(X1)),sK5(X1)) ) ),
    inference(resolution,[],[f1811,f538])).

fof(f1811,plain,(
    ! [X3] :
      ( ~ r2_hidden(k1_zfmisc_1(sK3(sK5(X3))),sK5(X3))
      | ~ r2_hidden(sK0,sK5(X3))
      | ~ r2_hidden(sK4(sK5(X3)),sK5(X3)) ) ),
    inference(subsumption_resolution,[],[f1810,f1632])).

fof(f1810,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK0,sK5(X3))
      | r2_hidden(sK2(sK5(X3)),sK5(X3))
      | ~ r2_hidden(k1_zfmisc_1(sK3(sK5(X3))),sK5(X3))
      | ~ r2_hidden(sK4(sK5(X3)),sK5(X3)) ) ),
    inference(duplicate_literal_removal,[],[f1763])).

fof(f1763,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK0,sK5(X3))
      | r2_hidden(sK2(sK5(X3)),sK5(X3))
      | ~ r2_hidden(sK0,sK5(X3))
      | ~ r2_hidden(k1_zfmisc_1(sK3(sK5(X3))),sK5(X3))
      | ~ r2_hidden(sK4(sK5(X3)),sK5(X3)) ) ),
    inference(resolution,[],[f1701,f30])).

fof(f30,plain,(
    ! [X1] :
      ( r1_tarski(sK2(X1),sK1(X1))
      | ~ r2_hidden(sK0,X1)
      | ~ r2_hidden(k1_zfmisc_1(sK3(X1)),X1)
      | ~ r2_hidden(sK4(X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3241,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,sK5(X0))
      | ~ r1_tarski(sK4(sK5(X0)),sK5(X0))
      | r2_hidden(sK4(sK5(X0)),sK5(X0)) ) ),
    inference(resolution,[],[f3190,f42])).

fof(f3190,plain,(
    ! [X1] :
      ( ~ r2_tarski(sK4(sK5(X1)),sK5(X1))
      | ~ r2_hidden(sK0,sK5(X1)) ) ),
    inference(subsumption_resolution,[],[f3187,f1815])).

fof(f1815,plain,(
    ! [X7] :
      ( ~ r2_tarski(sK4(sK5(X7)),sK5(X7))
      | r2_hidden(sK3(sK5(X7)),sK5(X7))
      | ~ r2_hidden(sK0,sK5(X7)) ) ),
    inference(subsumption_resolution,[],[f1806,f1631])).

fof(f1631,plain,(
    ! [X7] :
      ( ~ r2_tarski(sK4(sK5(X7)),sK5(X7))
      | ~ r2_hidden(sK0,sK5(X7))
      | ~ r2_hidden(sK2(sK5(X7)),sK5(X7)) ) ),
    inference(subsumption_resolution,[],[f1616,f38])).

fof(f1616,plain,(
    ! [X7] :
      ( ~ r2_hidden(sK3(sK5(X7)),sK5(X7))
      | ~ r2_hidden(sK2(sK5(X7)),sK5(X7))
      | ~ r2_hidden(sK0,sK5(X7))
      | ~ r2_tarski(sK4(sK5(X7)),sK5(X7)) ) ),
    inference(resolution,[],[f538,f35])).

fof(f35,plain,(
    ! [X1] :
      ( ~ r2_hidden(k1_zfmisc_1(sK3(X1)),X1)
      | ~ r2_hidden(sK2(X1),X1)
      | ~ r2_hidden(sK0,X1)
      | ~ r2_tarski(sK4(X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1806,plain,(
    ! [X7] :
      ( ~ r2_hidden(sK0,sK5(X7))
      | r2_hidden(sK2(sK5(X7)),sK5(X7))
      | r2_hidden(sK3(sK5(X7)),sK5(X7))
      | ~ r2_tarski(sK4(sK5(X7)),sK5(X7)) ) ),
    inference(duplicate_literal_removal,[],[f1767])).

fof(f1767,plain,(
    ! [X7] :
      ( ~ r2_hidden(sK0,sK5(X7))
      | r2_hidden(sK2(sK5(X7)),sK5(X7))
      | ~ r2_hidden(sK0,sK5(X7))
      | r2_hidden(sK3(sK5(X7)),sK5(X7))
      | ~ r2_tarski(sK4(sK5(X7)),sK5(X7)) ) ),
    inference(resolution,[],[f1701,f32])).

fof(f3187,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK0,sK5(X1))
      | ~ r2_tarski(sK4(sK5(X1)),sK5(X1))
      | ~ r2_hidden(sK3(sK5(X1)),sK5(X1)) ) ),
    inference(resolution,[],[f1812,f538])).

fof(f1812,plain,(
    ! [X4] :
      ( ~ r2_hidden(k1_zfmisc_1(sK3(sK5(X4))),sK5(X4))
      | ~ r2_hidden(sK0,sK5(X4))
      | ~ r2_tarski(sK4(sK5(X4)),sK5(X4)) ) ),
    inference(subsumption_resolution,[],[f1809,f1631])).

fof(f1809,plain,(
    ! [X4] :
      ( ~ r2_hidden(sK0,sK5(X4))
      | r2_hidden(sK2(sK5(X4)),sK5(X4))
      | ~ r2_hidden(k1_zfmisc_1(sK3(sK5(X4))),sK5(X4))
      | ~ r2_tarski(sK4(sK5(X4)),sK5(X4)) ) ),
    inference(duplicate_literal_removal,[],[f1764])).

fof(f1764,plain,(
    ! [X4] :
      ( ~ r2_hidden(sK0,sK5(X4))
      | r2_hidden(sK2(sK5(X4)),sK5(X4))
      | ~ r2_hidden(sK0,sK5(X4))
      | ~ r2_hidden(k1_zfmisc_1(sK3(sK5(X4))),sK5(X4))
      | ~ r2_tarski(sK4(sK5(X4)),sK5(X4)) ) ),
    inference(resolution,[],[f1701,f29])).

fof(f29,plain,(
    ! [X1] :
      ( r1_tarski(sK2(X1),sK1(X1))
      | ~ r2_hidden(sK0,X1)
      | ~ r2_hidden(k1_zfmisc_1(sK3(X1)),X1)
      | ~ r2_tarski(sK4(X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3329,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK0,sK5(X1))
      | r1_tarski(sK4(sK5(X1)),sK5(X1))
      | ~ r2_hidden(sK3(sK5(X1)),sK5(X1)) ) ),
    inference(resolution,[],[f1813,f538])).

fof(f1813,plain,(
    ! [X5] :
      ( ~ r2_hidden(k1_zfmisc_1(sK3(sK5(X5))),sK5(X5))
      | ~ r2_hidden(sK0,sK5(X5))
      | r1_tarski(sK4(sK5(X5)),sK5(X5)) ) ),
    inference(subsumption_resolution,[],[f1808,f1630])).

fof(f1630,plain,(
    ! [X6] :
      ( r1_tarski(sK4(sK5(X6)),sK5(X6))
      | ~ r2_hidden(sK0,sK5(X6))
      | ~ r2_hidden(sK2(sK5(X6)),sK5(X6)) ) ),
    inference(subsumption_resolution,[],[f1615,f37])).

fof(f1615,plain,(
    ! [X6] :
      ( ~ r2_hidden(sK3(sK5(X6)),sK5(X6))
      | ~ r2_hidden(sK2(sK5(X6)),sK5(X6))
      | ~ r2_hidden(sK0,sK5(X6))
      | r1_tarski(sK4(sK5(X6)),sK5(X6)) ) ),
    inference(resolution,[],[f538,f34])).

fof(f34,plain,(
    ! [X1] :
      ( ~ r2_hidden(k1_zfmisc_1(sK3(X1)),X1)
      | ~ r2_hidden(sK2(X1),X1)
      | ~ r2_hidden(sK0,X1)
      | r1_tarski(sK4(X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1808,plain,(
    ! [X5] :
      ( ~ r2_hidden(sK0,sK5(X5))
      | r2_hidden(sK2(sK5(X5)),sK5(X5))
      | ~ r2_hidden(k1_zfmisc_1(sK3(sK5(X5))),sK5(X5))
      | r1_tarski(sK4(sK5(X5)),sK5(X5)) ) ),
    inference(duplicate_literal_removal,[],[f1765])).

fof(f1765,plain,(
    ! [X5] :
      ( ~ r2_hidden(sK0,sK5(X5))
      | r2_hidden(sK2(sK5(X5)),sK5(X5))
      | ~ r2_hidden(sK0,sK5(X5))
      | ~ r2_hidden(k1_zfmisc_1(sK3(sK5(X5))),sK5(X5))
      | r1_tarski(sK4(sK5(X5)),sK5(X5)) ) ),
    inference(resolution,[],[f1701,f28])).

fof(f28,plain,(
    ! [X1] :
      ( r1_tarski(sK2(X1),sK1(X1))
      | ~ r2_hidden(sK0,X1)
      | ~ r2_hidden(k1_zfmisc_1(sK3(X1)),X1)
      | r1_tarski(sK4(X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
