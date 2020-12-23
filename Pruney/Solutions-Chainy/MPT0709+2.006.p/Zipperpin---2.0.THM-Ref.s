%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nnkOaYS1Bt

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:06 EST 2020

% Result     : Theorem 54.22s
% Output     : Refutation 54.22s
% Verified   : 
% Statistics : Number of formulae       :  343 (8519 expanded)
%              Number of leaves         :   47 (2784 expanded)
%              Depth                    :   52
%              Number of atoms          : 2768 (83347 expanded)
%              Number of equality atoms :  159 (6053 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(t164_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
            & ( v2_funct_1 @ B ) )
         => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t164_funct_1])).

thf('0',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X64: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X64 ) )
      | ~ ( v1_funct_1 @ X64 )
      | ~ ( v1_relat_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('2',plain,(
    ! [X64: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X64 ) )
      | ~ ( v1_funct_1 @ X64 )
      | ~ ( v1_relat_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X57: $i] :
      ( ( ( k10_relat_1 @ X57 @ ( k2_relat_1 @ X57 ) )
        = ( k1_relat_1 @ X57 ) )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('4',plain,(
    ! [X74: $i,X75: $i] :
      ( ~ ( v2_funct_1 @ X74 )
      | ( ( k10_relat_1 @ X74 @ X75 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X74 ) @ X75 ) )
      | ~ ( v1_funct_1 @ X74 )
      | ~ ( v1_relat_1 @ X74 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('5',plain,(
    ! [X64: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X64 ) )
      | ~ ( v1_funct_1 @ X64 )
      | ~ ( v1_relat_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('6',plain,(
    ! [X64: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X64 ) )
      | ~ ( v1_funct_1 @ X64 )
      | ~ ( v1_relat_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('7',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X47 @ X48 ) @ ( k2_relat_1 @ X47 ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf(t154_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k9_relat_1 @ B @ A )
          = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('8',plain,(
    ! [X72: $i,X73: $i] :
      ( ~ ( v2_funct_1 @ X72 )
      | ( ( k9_relat_1 @ X72 @ X73 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X72 ) @ X73 ) )
      | ~ ( v1_funct_1 @ X72 )
      | ~ ( v1_relat_1 @ X72 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('9',plain,(
    ! [X57: $i] :
      ( ( ( k10_relat_1 @ X57 @ ( k2_relat_1 @ X57 ) )
        = ( k1_relat_1 @ X57 ) )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t170_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ B @ ( k2_relat_1 @ B ) ) ) ) )).

thf('10',plain,(
    ! [X58: $i,X59: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X58 @ X59 ) @ ( k10_relat_1 @ X58 @ ( k2_relat_1 @ X58 ) ) )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t170_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X64: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X64 ) )
      | ~ ( v1_funct_1 @ X64 )
      | ~ ( v1_relat_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(s3_funct_1__e2_24__funct_1,axiom,(
    ! [A: $i,B: $i] :
    ? [C: $i] :
      ( ! [D: $i] :
          ( ( r2_hidden @ D @ A )
         => ( ( k1_funct_1 @ C @ D )
            = B ) )
      & ( ( k1_relat_1 @ C )
        = A )
      & ( v1_funct_1 @ C )
      & ( v1_relat_1 @ C ) ) )).

thf('21',plain,(
    ! [X65: $i,X66: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X65 @ X66 ) )
      = X66 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('22',plain,(
    ! [X17: $i] :
      ( r1_tarski @ k1_xboole_0 @ X17 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('23',plain,(
    ! [X62: $i,X63: $i] :
      ( ~ ( r1_tarski @ X62 @ ( k1_relat_1 @ X63 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X63 @ X62 ) )
        = X62 )
      | ~ ( v1_relat_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('25',plain,(
    ! [X60: $i,X61: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X60 @ X61 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X60 ) @ X61 ) )
      | ~ ( v1_relat_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X45 @ X46 ) )
      = ( k3_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('27',plain,(
    ! [X60: $i,X61: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X60 @ X61 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ X60 ) @ X61 ) ) )
      | ~ ( v1_relat_1 @ X60 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ X0 ) @ k1_xboole_0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ X0 ) @ k1_xboole_0 ) ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','29'])).

thf('31',plain,(
    ! [X65: $i,X66: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X65 @ X66 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('33',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C_1 @ X7 @ X6 ) @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('34',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X45 @ X46 ) )
      = ( k3_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('35',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C_1 @ X7 @ X6 ) @ ( k1_setfam_1 @ ( k2_tarski @ X6 @ X7 ) ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X65: $i,X66: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X65 @ X66 ) )
      = X66 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('38',plain,(
    ! [X55: $i,X56: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X55 @ X56 ) @ ( k1_relat_1 @ X55 ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( sk_C_2 @ X1 @ X0 ) @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X65: $i,X66: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X65 @ X66 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( sk_C_2 @ X1 @ X0 ) @ X2 ) @ X0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X17: $i] :
      ( r1_tarski @ k1_xboole_0 @ X17 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('43',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( sk_C_2 @ X1 @ k1_xboole_0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('46',plain,(
    ! [X68: $i,X69: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X68 @ ( k10_relat_1 @ X68 @ X69 ) ) @ X69 )
      | ~ ( v1_funct_1 @ X68 )
      | ~ ( v1_relat_1 @ X68 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( sk_C_2 @ X1 @ k1_xboole_0 ) @ k1_xboole_0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X65: $i,X66: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X65 @ X66 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('49',plain,(
    ! [X65: $i,X66: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X65 @ X66 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_relat_1 @ ( sk_C_2 @ X1 @ k1_xboole_0 ) @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X65: $i,X66: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X65 @ X66 ) )
      = X66 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('54',plain,(
    ! [X49: $i] :
      ( ( ( k9_relat_1 @ X49 @ ( k1_relat_1 @ X49 ) )
        = ( k2_relat_1 @ X49 ) )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( sk_C_2 @ X1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X65: $i,X66: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X65 @ X66 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( sk_C_2 @ X1 @ X0 ) @ X0 )
      = ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','57'])).

thf('59',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X47 @ X48 ) @ ( k2_relat_1 @ X47 ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('60',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k9_relat_1 @ ( sk_C_2 @ X1 @ k1_xboole_0 ) @ X0 ) )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ k1_xboole_0 ) )
        = ( k9_relat_1 @ ( sk_C_2 @ X1 @ k1_xboole_0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X17: $i] :
      ( r1_tarski @ k1_xboole_0 @ X17 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','57'])).

thf('65',plain,(
    ! [X65: $i,X66: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X65 @ X66 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k9_relat_1 @ ( sk_C_2 @ X1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63','64','65'])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('67',plain,(
    ! [X50: $i,X51: $i] :
      ( ( ( k9_relat_1 @ X50 @ X51 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X50 ) @ X51 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ k1_xboole_0 ) )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( sk_C_2 @ X1 @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X65: $i,X66: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X65 @ X66 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('70',plain,(
    ! [X65: $i,X66: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X65 @ X66 ) )
      = X66 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X65: $i,X66: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X65 @ X66 ) )
      = X66 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ X0 ) @ k1_xboole_0 ) ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('75',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X6 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('76',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X45 @ X46 ) )
      = ( k3_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('77',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k1_setfam_1 @ ( k2_tarski @ X6 @ X9 ) ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k1_relat_1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['73','78'])).

thf('80',plain,(
    ! [X65: $i,X66: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X65 @ X66 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('81',plain,(
    ! [X0: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['36','82'])).

thf('84',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X50 ) @ X51 )
      | ( ( k9_relat_1 @ X50 @ X51 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X74: $i,X75: $i] :
      ( ~ ( v2_funct_1 @ X74 )
      | ( ( k10_relat_1 @ X74 @ X75 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X74 ) @ X75 ) )
      | ~ ( v1_funct_1 @ X74 )
      | ~ ( v1_relat_1 @ X74 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X55: $i,X56: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X55 @ X56 ) @ ( k1_relat_1 @ X55 ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('91',plain,(
    ! [X62: $i,X63: $i] :
      ( ~ ( r1_tarski @ X62 @ ( k1_relat_1 @ X63 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X63 @ X62 ) )
        = X62 )
      | ~ ( v1_relat_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) ) )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) ) )
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k10_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['89','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k10_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ! [X65: $i,X66: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X65 @ X66 ) )
      = X66 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('97',plain,(
    ! [X68: $i,X69: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X68 @ ( k10_relat_1 @ X68 @ X69 ) ) @ X69 )
      | ~ ( v1_funct_1 @ X68 )
      | ~ ( v1_relat_1 @ X68 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X50: $i,X51: $i] :
      ( ( ( k9_relat_1 @ X50 @ X51 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X50 ) @ X51 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k10_relat_1 @ ( sk_C_2 @ X1 @ X0 ) @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['96','102'])).

thf('104',plain,(
    ! [X65: $i,X66: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X65 @ X66 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('105',plain,(
    ! [X65: $i,X66: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X65 @ X66 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k10_relat_1 @ ( sk_C_2 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('107',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('108',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k1_setfam_1 @ ( k2_tarski @ X6 @ X9 ) ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k10_relat_1 @ ( sk_C_2 @ X1 @ X0 ) @ k1_xboole_0 ) ) ) @ X2 ) ),
    inference('sup-',[status(thm)],['106','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k10_relat_1 @ ( sk_C_2 @ X1 @ X0 ) @ k1_xboole_0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X65: $i,X66: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X65 @ X66 ) )
      = X66 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('114',plain,(
    ! [X60: $i,X61: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X60 @ X61 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ X60 ) @ X61 ) ) )
      | ~ ( v1_relat_1 @ X60 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) ) )
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ X1 ) @ ( k10_relat_1 @ X1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ X1 ) @ ( k10_relat_1 @ X1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k10_relat_1 @ ( sk_C_2 @ X2 @ X0 ) @ X1 ) ) )
        = ( k10_relat_1 @ ( sk_C_2 @ X2 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['113','117'])).

thf('119',plain,(
    ! [X65: $i,X66: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X65 @ X66 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k10_relat_1 @ ( sk_C_2 @ X2 @ X0 ) @ X1 ) ) )
      = ( k10_relat_1 @ ( sk_C_2 @ X2 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( sk_C_2 @ X1 @ X0 ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['112','120'])).

thf('122',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( sk_C_2 @ X1 @ X0 ) @ X2 ) @ X0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('124',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( sk_C_2 @ X2 @ X0 ) @ X1 ) @ X3 )
      | ~ ( r1_tarski @ X0 @ X3 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( sk_C_2 @ X1 @ sk_A ) @ X0 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['122','125'])).

thf('127',plain,(
    ! [X62: $i,X63: $i] :
      ( ~ ( r1_tarski @ X62 @ ( k1_relat_1 @ X63 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X63 @ X62 ) )
        = X62 )
      | ~ ( v1_relat_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k10_relat_1 @ ( sk_C_2 @ X1 @ sk_A ) @ X0 ) ) )
        = ( k10_relat_1 @ ( sk_C_2 @ X1 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k10_relat_1 @ ( sk_C_2 @ X1 @ sk_A ) @ X0 ) ) )
      = ( k10_relat_1 @ ( sk_C_2 @ X1 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ k1_xboole_0 ) )
      = ( k10_relat_1 @ ( sk_C_2 @ X0 @ sk_A ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['121','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( sk_C_2 @ X1 @ X0 ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['112','120'])).

thf('133',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( ( k10_relat_1 @ sk_B @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['95','133'])).

thf('135',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( k10_relat_1 @ sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['134','135','136','137'])).

thf('139',plain,(
    ! [X68: $i,X69: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X68 @ ( k10_relat_1 @ X68 @ X69 ) ) @ X69 )
      | ~ ( v1_funct_1 @ X68 )
      | ~ ( v1_relat_1 @ X68 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('140',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k9_relat_1 @ sk_B @ k1_xboole_0 ) )
    | ( k1_xboole_0
      = ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ k1_xboole_0 ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['138','141'])).

thf('143',plain,(
    ! [X17: $i] :
      ( r1_tarski @ k1_xboole_0 @ X17 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('144',plain,
    ( ( k10_relat_1 @ sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['134','135','136','137'])).

thf('145',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( k1_xboole_0
    = ( k9_relat_1 @ sk_B @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['142','143','144','145','146'])).

thf('148',plain,(
    ! [X49: $i] :
      ( ( ( k9_relat_1 @ X49 @ ( k1_relat_1 @ X49 ) )
        = ( k2_relat_1 @ X49 ) )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t153_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k9_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('149',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( ( k9_relat_1 @ X52 @ ( k2_xboole_0 @ X53 @ X54 ) )
        = ( k2_xboole_0 @ ( k9_relat_1 @ X52 @ X53 ) @ ( k9_relat_1 @ X52 @ X54 ) ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t153_relat_1])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k2_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X0 ) @ ( k9_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k2_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X0 ) @ ( k9_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_B ) @ k1_xboole_0 ) )
      = ( k2_xboole_0 @ ( k2_relat_1 @ sk_B ) @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['147','151'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('155',plain,(
    ! [X13: $i] :
      ( ( k2_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['154','155'])).

thf('159',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['152','153','156','157','158','159'])).

thf('161',plain,(
    ! [X64: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X64 ) )
      | ~ ( v1_funct_1 @ X64 )
      | ~ ( v1_relat_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('162',plain,(
    ! [X72: $i,X73: $i] :
      ( ~ ( v2_funct_1 @ X72 )
      | ( ( k9_relat_1 @ X72 @ X73 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X72 ) @ X73 ) )
      | ~ ( v1_funct_1 @ X72 )
      | ~ ( v1_relat_1 @ X72 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('163',plain,(
    ! [X55: $i,X56: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X55 @ X56 ) @ ( k1_relat_1 @ X55 ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['161','164'])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['165'])).

thf('167',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k2_relat_1 @ sk_B ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) )
      = ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['160','168'])).

thf('170',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['152','153','156','157','158','159'])).

thf('171',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k2_relat_1 @ sk_B ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) )
      = ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['169','170','171','172','173'])).

thf('175',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) )
      = ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','174'])).

thf('176',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['175','176','177','178'])).

thf('180',plain,(
    ! [X49: $i] :
      ( ( ( k9_relat_1 @ X49 @ ( k1_relat_1 @ X49 ) )
        = ( k2_relat_1 @ X49 ) )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('181',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k2_relat_1 @ sk_B ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['179','180'])).

thf('182',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k2_relat_1 @ sk_B ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','181'])).

thf('183',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k2_relat_1 @ sk_B ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['182','183','184'])).

thf('186',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['4','185'])).

thf('187',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['186','187','188','189'])).

thf('191',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','190'])).

thf('192',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['191','192'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('194',plain,(
    ! [X70: $i,X71: $i] :
      ( ~ ( r1_tarski @ X70 @ ( k2_relat_1 @ X71 ) )
      | ( ( k9_relat_1 @ X71 @ ( k10_relat_1 @ X71 @ X70 ) )
        = X70 )
      | ~ ( v1_funct_1 @ X71 )
      | ~ ( v1_relat_1 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('195',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X72: $i,X73: $i] :
      ( ~ ( v2_funct_1 @ X72 )
      | ( ( k9_relat_1 @ X72 @ X73 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X72 ) @ X73 ) )
      | ~ ( v1_funct_1 @ X72 )
      | ~ ( v1_relat_1 @ X72 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('197',plain,(
    ! [X64: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X64 ) )
      | ~ ( v1_funct_1 @ X64 )
      | ~ ( v1_relat_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('198',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['175','176','177','178'])).

thf('199',plain,(
    ! [X55: $i,X56: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X55 @ X56 ) @ ( k1_relat_1 @ X55 ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('200',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) @ ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['197','200'])).

thf('202',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['201','202','203'])).

thf('205',plain,(
    ! [X70: $i,X71: $i] :
      ( ~ ( r1_tarski @ X70 @ ( k2_relat_1 @ X71 ) )
      | ( ( k9_relat_1 @ X71 @ ( k10_relat_1 @ X71 @ X70 ) )
        = X70 )
      | ~ ( v1_funct_1 @ X71 )
      | ~ ( v1_relat_1 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('206',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) ) )
        = ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) ) )
      = ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['206','207','208'])).

thf('210',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ X0 ) ) )
        = ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['196','209'])).

thf('211',plain,(
    ! [X72: $i,X73: $i] :
      ( ~ ( v2_funct_1 @ X72 )
      | ( ( k9_relat_1 @ X72 @ X73 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X72 ) @ X73 ) )
      | ~ ( v1_funct_1 @ X72 )
      | ~ ( v1_relat_1 @ X72 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('212',plain,(
    ! [X64: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X64 ) )
      | ~ ( v1_funct_1 @ X64 )
      | ~ ( v1_relat_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('213',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('214',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['152','153','156','157','158','159'])).

thf('215',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['165'])).

thf('216',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['214','215'])).

thf('217',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['216','217','218','219'])).

thf('221',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('222',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['220','221'])).

thf('223',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['213','222'])).

thf('224',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['212','223'])).

thf('225',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['224','225','226'])).

thf('228',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['211','227'])).

thf('229',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['228','229','230','231'])).

thf('233',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X47 @ X48 ) @ ( k2_relat_1 @ X47 ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('234',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('235',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['233','234'])).

thf('236',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_B @ X0 ) @ ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['232','235'])).

thf('237',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_B @ X0 ) @ ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['236','237'])).

thf('239',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['228','229','230','231'])).

thf('240',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('241',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['239','240'])).

thf('242',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['241','242'])).

thf('244',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_B @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['238','243'])).

thf('245',plain,(
    ! [X70: $i,X71: $i] :
      ( ~ ( r1_tarski @ X70 @ ( k2_relat_1 @ X71 ) )
      | ( ( k9_relat_1 @ X71 @ ( k10_relat_1 @ X71 @ X70 ) )
        = X70 )
      | ~ ( v1_funct_1 @ X71 )
      | ~ ( v1_relat_1 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('246',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ X0 ) ) )
        = ( k9_relat_1 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['244','245'])).

thf('247',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ X0 ) ) )
      = ( k9_relat_1 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['246','247','248'])).

thf('250',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_B @ X0 )
      = ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['210','249','250','251','252'])).

thf('254',plain,(
    ! [X74: $i,X75: $i] :
      ( ~ ( v2_funct_1 @ X74 )
      | ( ( k10_relat_1 @ X74 @ X75 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X74 ) @ X75 ) )
      | ~ ( v1_funct_1 @ X74 )
      | ~ ( v1_relat_1 @ X74 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('255',plain,(
    ! [X64: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X64 ) )
      | ~ ( v1_funct_1 @ X64 )
      | ~ ( v1_relat_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('256',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['191','192'])).

thf('257',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X47 @ X48 ) @ ( k2_relat_1 @ X47 ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('258',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['256','257'])).

thf('259',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( r1_tarski @ ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['255','258'])).

thf('260',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['259','260','261'])).

thf('263',plain,(
    ! [X62: $i,X63: $i] :
      ( ~ ( r1_tarski @ X62 @ ( k1_relat_1 @ X63 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X63 @ X62 ) )
        = X62 )
      | ~ ( v1_relat_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('264',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) ) )
        = ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['262','263'])).

thf('265',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('266',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) ) )
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['264','265'])).

thf('267',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ X0 ) ) )
        = ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['254','266'])).

thf('268',plain,
    ( ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['186','187','188','189'])).

thf('269',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['191','192'])).

thf('270',plain,
    ( ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['268','269'])).

thf('271',plain,(
    ! [X58: $i,X59: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X58 @ X59 ) @ ( k10_relat_1 @ X58 @ ( k2_relat_1 @ X58 ) ) )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t170_relat_1])).

thf('272',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['270','271'])).

thf('273',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('274',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['272','273'])).

thf('275',plain,(
    ! [X62: $i,X63: $i] :
      ( ~ ( r1_tarski @ X62 @ ( k1_relat_1 @ X63 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X63 @ X62 ) )
        = X62 )
      | ~ ( v1_relat_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('276',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ X0 ) ) )
        = ( k10_relat_1 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['274','275'])).

thf('277',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('278',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ X0 ) ) )
      = ( k10_relat_1 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['276','277'])).

thf('279',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('280',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('282',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_B @ X0 )
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['267','278','279','280','281'])).

thf('283',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
      | ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['195','253','282'])).

thf('284',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','283'])).

thf('285',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('286',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('287',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['284','285','286'])).

thf('288',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['1','287'])).

thf('289',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('290',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('291',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['288','289','290'])).

thf('292',plain,
    ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['0','291'])).

thf('293',plain,(
    ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('294',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['292','293'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nnkOaYS1Bt
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:47:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 54.22/54.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 54.22/54.46  % Solved by: fo/fo7.sh
% 54.22/54.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 54.22/54.46  % done 46210 iterations in 53.994s
% 54.22/54.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 54.22/54.46  % SZS output start Refutation
% 54.22/54.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 54.22/54.46  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 54.22/54.46  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 54.22/54.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 54.22/54.46  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 54.22/54.46  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 54.22/54.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 54.22/54.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 54.22/54.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 54.22/54.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 54.22/54.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 54.22/54.46  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 54.22/54.46  thf(sk_B_type, type, sk_B: $i).
% 54.22/54.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 54.22/54.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 54.22/54.46  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 54.22/54.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 54.22/54.46  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 54.22/54.46  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 54.22/54.46  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 54.22/54.46  thf(sk_A_type, type, sk_A: $i).
% 54.22/54.46  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 54.22/54.46  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 54.22/54.46  thf(t164_funct_1, conjecture,
% 54.22/54.46    (![A:$i,B:$i]:
% 54.22/54.46     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 54.22/54.46       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 54.22/54.46         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 54.22/54.46  thf(zf_stmt_0, negated_conjecture,
% 54.22/54.46    (~( ![A:$i,B:$i]:
% 54.22/54.46        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 54.22/54.46          ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 54.22/54.46            ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ) )),
% 54.22/54.46    inference('cnf.neg', [status(esa)], [t164_funct_1])).
% 54.22/54.46  thf('0', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf(dt_k2_funct_1, axiom,
% 54.22/54.46    (![A:$i]:
% 54.22/54.46     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 54.22/54.46       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 54.22/54.46         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 54.22/54.46  thf('1', plain,
% 54.22/54.46      (![X64 : $i]:
% 54.22/54.46         ((v1_funct_1 @ (k2_funct_1 @ X64))
% 54.22/54.46          | ~ (v1_funct_1 @ X64)
% 54.22/54.46          | ~ (v1_relat_1 @ X64))),
% 54.22/54.46      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 54.22/54.46  thf('2', plain,
% 54.22/54.46      (![X64 : $i]:
% 54.22/54.46         ((v1_relat_1 @ (k2_funct_1 @ X64))
% 54.22/54.46          | ~ (v1_funct_1 @ X64)
% 54.22/54.46          | ~ (v1_relat_1 @ X64))),
% 54.22/54.46      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 54.22/54.46  thf(t169_relat_1, axiom,
% 54.22/54.46    (![A:$i]:
% 54.22/54.46     ( ( v1_relat_1 @ A ) =>
% 54.22/54.46       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 54.22/54.46  thf('3', plain,
% 54.22/54.46      (![X57 : $i]:
% 54.22/54.46         (((k10_relat_1 @ X57 @ (k2_relat_1 @ X57)) = (k1_relat_1 @ X57))
% 54.22/54.46          | ~ (v1_relat_1 @ X57))),
% 54.22/54.46      inference('cnf', [status(esa)], [t169_relat_1])).
% 54.22/54.46  thf(t155_funct_1, axiom,
% 54.22/54.46    (![A:$i,B:$i]:
% 54.22/54.46     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 54.22/54.46       ( ( v2_funct_1 @ B ) =>
% 54.22/54.46         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 54.22/54.46  thf('4', plain,
% 54.22/54.46      (![X74 : $i, X75 : $i]:
% 54.22/54.46         (~ (v2_funct_1 @ X74)
% 54.22/54.46          | ((k10_relat_1 @ X74 @ X75)
% 54.22/54.46              = (k9_relat_1 @ (k2_funct_1 @ X74) @ X75))
% 54.22/54.46          | ~ (v1_funct_1 @ X74)
% 54.22/54.46          | ~ (v1_relat_1 @ X74))),
% 54.22/54.46      inference('cnf', [status(esa)], [t155_funct_1])).
% 54.22/54.46  thf('5', plain,
% 54.22/54.46      (![X64 : $i]:
% 54.22/54.46         ((v1_relat_1 @ (k2_funct_1 @ X64))
% 54.22/54.46          | ~ (v1_funct_1 @ X64)
% 54.22/54.46          | ~ (v1_relat_1 @ X64))),
% 54.22/54.46      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 54.22/54.46  thf('6', plain,
% 54.22/54.46      (![X64 : $i]:
% 54.22/54.46         ((v1_relat_1 @ (k2_funct_1 @ X64))
% 54.22/54.46          | ~ (v1_funct_1 @ X64)
% 54.22/54.46          | ~ (v1_relat_1 @ X64))),
% 54.22/54.46      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 54.22/54.46  thf(t144_relat_1, axiom,
% 54.22/54.46    (![A:$i,B:$i]:
% 54.22/54.46     ( ( v1_relat_1 @ B ) =>
% 54.22/54.46       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 54.22/54.46  thf('7', plain,
% 54.22/54.46      (![X47 : $i, X48 : $i]:
% 54.22/54.46         ((r1_tarski @ (k9_relat_1 @ X47 @ X48) @ (k2_relat_1 @ X47))
% 54.22/54.46          | ~ (v1_relat_1 @ X47))),
% 54.22/54.46      inference('cnf', [status(esa)], [t144_relat_1])).
% 54.22/54.46  thf(t154_funct_1, axiom,
% 54.22/54.46    (![A:$i,B:$i]:
% 54.22/54.46     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 54.22/54.46       ( ( v2_funct_1 @ B ) =>
% 54.22/54.46         ( ( k9_relat_1 @ B @ A ) = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 54.22/54.46  thf('8', plain,
% 54.22/54.46      (![X72 : $i, X73 : $i]:
% 54.22/54.46         (~ (v2_funct_1 @ X72)
% 54.22/54.46          | ((k9_relat_1 @ X72 @ X73)
% 54.22/54.46              = (k10_relat_1 @ (k2_funct_1 @ X72) @ X73))
% 54.22/54.46          | ~ (v1_funct_1 @ X72)
% 54.22/54.46          | ~ (v1_relat_1 @ X72))),
% 54.22/54.46      inference('cnf', [status(esa)], [t154_funct_1])).
% 54.22/54.46  thf('9', plain,
% 54.22/54.46      (![X57 : $i]:
% 54.22/54.46         (((k10_relat_1 @ X57 @ (k2_relat_1 @ X57)) = (k1_relat_1 @ X57))
% 54.22/54.46          | ~ (v1_relat_1 @ X57))),
% 54.22/54.46      inference('cnf', [status(esa)], [t169_relat_1])).
% 54.22/54.46  thf(t170_relat_1, axiom,
% 54.22/54.46    (![A:$i,B:$i]:
% 54.22/54.46     ( ( v1_relat_1 @ B ) =>
% 54.22/54.46       ( r1_tarski @
% 54.22/54.46         ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ B @ ( k2_relat_1 @ B ) ) ) ))).
% 54.22/54.46  thf('10', plain,
% 54.22/54.46      (![X58 : $i, X59 : $i]:
% 54.22/54.46         ((r1_tarski @ (k10_relat_1 @ X58 @ X59) @ 
% 54.22/54.46           (k10_relat_1 @ X58 @ (k2_relat_1 @ X58)))
% 54.22/54.46          | ~ (v1_relat_1 @ X58))),
% 54.22/54.46      inference('cnf', [status(esa)], [t170_relat_1])).
% 54.22/54.46  thf('11', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         ((r1_tarski @ (k1_relat_1 @ X0) @ 
% 54.22/54.46           (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 54.22/54.46          | ~ (v1_relat_1 @ X0)
% 54.22/54.46          | ~ (v1_relat_1 @ X0))),
% 54.22/54.46      inference('sup+', [status(thm)], ['9', '10'])).
% 54.22/54.46  thf('12', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         (~ (v1_relat_1 @ X0)
% 54.22/54.46          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 54.22/54.46             (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 54.22/54.46      inference('simplify', [status(thm)], ['11'])).
% 54.22/54.46  thf(t1_xboole_1, axiom,
% 54.22/54.46    (![A:$i,B:$i,C:$i]:
% 54.22/54.46     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 54.22/54.46       ( r1_tarski @ A @ C ) ))).
% 54.22/54.46  thf('13', plain,
% 54.22/54.46      (![X14 : $i, X15 : $i, X16 : $i]:
% 54.22/54.46         (~ (r1_tarski @ X14 @ X15)
% 54.22/54.46          | ~ (r1_tarski @ X15 @ X16)
% 54.22/54.46          | (r1_tarski @ X14 @ X16))),
% 54.22/54.46      inference('cnf', [status(esa)], [t1_xboole_1])).
% 54.22/54.46  thf('14', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i]:
% 54.22/54.46         (~ (v1_relat_1 @ X0)
% 54.22/54.46          | (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 54.22/54.46          | ~ (r1_tarski @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) @ X1))),
% 54.22/54.46      inference('sup-', [status(thm)], ['12', '13'])).
% 54.22/54.46  thf('15', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i]:
% 54.22/54.46         (~ (r1_tarski @ 
% 54.22/54.46             (k9_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0))) @ X1)
% 54.22/54.46          | ~ (v1_relat_1 @ X0)
% 54.22/54.46          | ~ (v1_funct_1 @ X0)
% 54.22/54.46          | ~ (v2_funct_1 @ X0)
% 54.22/54.46          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ X1)
% 54.22/54.46          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 54.22/54.46      inference('sup-', [status(thm)], ['8', '14'])).
% 54.22/54.46  thf('16', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         (~ (v1_relat_1 @ X0)
% 54.22/54.46          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 54.22/54.46          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 54.22/54.46          | ~ (v2_funct_1 @ X0)
% 54.22/54.46          | ~ (v1_funct_1 @ X0)
% 54.22/54.46          | ~ (v1_relat_1 @ X0))),
% 54.22/54.46      inference('sup-', [status(thm)], ['7', '15'])).
% 54.22/54.46  thf('17', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         (~ (v1_funct_1 @ X0)
% 54.22/54.46          | ~ (v2_funct_1 @ X0)
% 54.22/54.46          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 54.22/54.46          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 54.22/54.46          | ~ (v1_relat_1 @ X0))),
% 54.22/54.46      inference('simplify', [status(thm)], ['16'])).
% 54.22/54.46  thf('18', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         (~ (v1_relat_1 @ X0)
% 54.22/54.46          | ~ (v1_funct_1 @ X0)
% 54.22/54.46          | ~ (v1_relat_1 @ X0)
% 54.22/54.46          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 54.22/54.46          | ~ (v2_funct_1 @ X0)
% 54.22/54.46          | ~ (v1_funct_1 @ X0))),
% 54.22/54.46      inference('sup-', [status(thm)], ['6', '17'])).
% 54.22/54.46  thf('19', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         (~ (v2_funct_1 @ X0)
% 54.22/54.46          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 54.22/54.46          | ~ (v1_funct_1 @ X0)
% 54.22/54.46          | ~ (v1_relat_1 @ X0))),
% 54.22/54.46      inference('simplify', [status(thm)], ['18'])).
% 54.22/54.46  thf('20', plain,
% 54.22/54.46      (![X64 : $i]:
% 54.22/54.46         ((v1_relat_1 @ (k2_funct_1 @ X64))
% 54.22/54.46          | ~ (v1_funct_1 @ X64)
% 54.22/54.46          | ~ (v1_relat_1 @ X64))),
% 54.22/54.46      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 54.22/54.46  thf(s3_funct_1__e2_24__funct_1, axiom,
% 54.22/54.46    (![A:$i,B:$i]:
% 54.22/54.46     ( ?[C:$i]:
% 54.22/54.46       ( ( ![D:$i]:
% 54.22/54.46           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 54.22/54.46         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 54.22/54.46         ( v1_relat_1 @ C ) ) ))).
% 54.22/54.46  thf('21', plain,
% 54.22/54.46      (![X65 : $i, X66 : $i]: ((k1_relat_1 @ (sk_C_2 @ X65 @ X66)) = (X66))),
% 54.22/54.46      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 54.22/54.46  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 54.22/54.46  thf('22', plain, (![X17 : $i]: (r1_tarski @ k1_xboole_0 @ X17)),
% 54.22/54.46      inference('cnf', [status(esa)], [t2_xboole_1])).
% 54.22/54.46  thf(t91_relat_1, axiom,
% 54.22/54.46    (![A:$i,B:$i]:
% 54.22/54.46     ( ( v1_relat_1 @ B ) =>
% 54.22/54.46       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 54.22/54.46         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 54.22/54.46  thf('23', plain,
% 54.22/54.46      (![X62 : $i, X63 : $i]:
% 54.22/54.46         (~ (r1_tarski @ X62 @ (k1_relat_1 @ X63))
% 54.22/54.46          | ((k1_relat_1 @ (k7_relat_1 @ X63 @ X62)) = (X62))
% 54.22/54.46          | ~ (v1_relat_1 @ X63))),
% 54.22/54.46      inference('cnf', [status(esa)], [t91_relat_1])).
% 54.22/54.46  thf('24', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         (~ (v1_relat_1 @ X0)
% 54.22/54.46          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 54.22/54.46      inference('sup-', [status(thm)], ['22', '23'])).
% 54.22/54.46  thf(t90_relat_1, axiom,
% 54.22/54.46    (![A:$i,B:$i]:
% 54.22/54.46     ( ( v1_relat_1 @ B ) =>
% 54.22/54.46       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 54.22/54.46         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 54.22/54.46  thf('25', plain,
% 54.22/54.46      (![X60 : $i, X61 : $i]:
% 54.22/54.46         (((k1_relat_1 @ (k7_relat_1 @ X60 @ X61))
% 54.22/54.46            = (k3_xboole_0 @ (k1_relat_1 @ X60) @ X61))
% 54.22/54.46          | ~ (v1_relat_1 @ X60))),
% 54.22/54.46      inference('cnf', [status(esa)], [t90_relat_1])).
% 54.22/54.46  thf(t12_setfam_1, axiom,
% 54.22/54.46    (![A:$i,B:$i]:
% 54.22/54.46     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 54.22/54.46  thf('26', plain,
% 54.22/54.46      (![X45 : $i, X46 : $i]:
% 54.22/54.46         ((k1_setfam_1 @ (k2_tarski @ X45 @ X46)) = (k3_xboole_0 @ X45 @ X46))),
% 54.22/54.46      inference('cnf', [status(esa)], [t12_setfam_1])).
% 54.22/54.46  thf('27', plain,
% 54.22/54.46      (![X60 : $i, X61 : $i]:
% 54.22/54.46         (((k1_relat_1 @ (k7_relat_1 @ X60 @ X61))
% 54.22/54.46            = (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ X60) @ X61)))
% 54.22/54.46          | ~ (v1_relat_1 @ X60))),
% 54.22/54.46      inference('demod', [status(thm)], ['25', '26'])).
% 54.22/54.46  thf('28', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         (((k1_xboole_0)
% 54.22/54.46            = (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ X0) @ k1_xboole_0)))
% 54.22/54.46          | ~ (v1_relat_1 @ X0)
% 54.22/54.46          | ~ (v1_relat_1 @ X0))),
% 54.22/54.46      inference('sup+', [status(thm)], ['24', '27'])).
% 54.22/54.46  thf('29', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         (~ (v1_relat_1 @ X0)
% 54.22/54.46          | ((k1_xboole_0)
% 54.22/54.46              = (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ X0) @ k1_xboole_0))))),
% 54.22/54.46      inference('simplify', [status(thm)], ['28'])).
% 54.22/54.46  thf('30', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i]:
% 54.22/54.46         (((k1_xboole_0) = (k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0)))
% 54.22/54.46          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0)))),
% 54.22/54.46      inference('sup+', [status(thm)], ['21', '29'])).
% 54.22/54.46  thf('31', plain,
% 54.22/54.46      (![X65 : $i, X66 : $i]: (v1_relat_1 @ (sk_C_2 @ X65 @ X66))),
% 54.22/54.46      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 54.22/54.46  thf('32', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         ((k1_xboole_0) = (k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0)))),
% 54.22/54.46      inference('demod', [status(thm)], ['30', '31'])).
% 54.22/54.46  thf(t4_xboole_0, axiom,
% 54.22/54.46    (![A:$i,B:$i]:
% 54.22/54.46     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 54.22/54.46            ( r1_xboole_0 @ A @ B ) ) ) & 
% 54.22/54.46       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 54.22/54.46            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 54.22/54.46  thf('33', plain,
% 54.22/54.46      (![X6 : $i, X7 : $i]:
% 54.22/54.46         ((r1_xboole_0 @ X6 @ X7)
% 54.22/54.46          | (r2_hidden @ (sk_C_1 @ X7 @ X6) @ (k3_xboole_0 @ X6 @ X7)))),
% 54.22/54.46      inference('cnf', [status(esa)], [t4_xboole_0])).
% 54.22/54.46  thf('34', plain,
% 54.22/54.46      (![X45 : $i, X46 : $i]:
% 54.22/54.46         ((k1_setfam_1 @ (k2_tarski @ X45 @ X46)) = (k3_xboole_0 @ X45 @ X46))),
% 54.22/54.46      inference('cnf', [status(esa)], [t12_setfam_1])).
% 54.22/54.46  thf('35', plain,
% 54.22/54.46      (![X6 : $i, X7 : $i]:
% 54.22/54.46         ((r1_xboole_0 @ X6 @ X7)
% 54.22/54.46          | (r2_hidden @ (sk_C_1 @ X7 @ X6) @ 
% 54.22/54.46             (k1_setfam_1 @ (k2_tarski @ X6 @ X7))))),
% 54.22/54.46      inference('demod', [status(thm)], ['33', '34'])).
% 54.22/54.46  thf('36', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 54.22/54.46          | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 54.22/54.46      inference('sup+', [status(thm)], ['32', '35'])).
% 54.22/54.46  thf('37', plain,
% 54.22/54.46      (![X65 : $i, X66 : $i]: ((k1_relat_1 @ (sk_C_2 @ X65 @ X66)) = (X66))),
% 54.22/54.46      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 54.22/54.46  thf(t167_relat_1, axiom,
% 54.22/54.46    (![A:$i,B:$i]:
% 54.22/54.46     ( ( v1_relat_1 @ B ) =>
% 54.22/54.46       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 54.22/54.46  thf('38', plain,
% 54.22/54.46      (![X55 : $i, X56 : $i]:
% 54.22/54.46         ((r1_tarski @ (k10_relat_1 @ X55 @ X56) @ (k1_relat_1 @ X55))
% 54.22/54.46          | ~ (v1_relat_1 @ X55))),
% 54.22/54.46      inference('cnf', [status(esa)], [t167_relat_1])).
% 54.22/54.46  thf('39', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.22/54.46         ((r1_tarski @ (k10_relat_1 @ (sk_C_2 @ X1 @ X0) @ X2) @ X0)
% 54.22/54.46          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0)))),
% 54.22/54.46      inference('sup+', [status(thm)], ['37', '38'])).
% 54.22/54.46  thf('40', plain,
% 54.22/54.46      (![X65 : $i, X66 : $i]: (v1_relat_1 @ (sk_C_2 @ X65 @ X66))),
% 54.22/54.46      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 54.22/54.46  thf('41', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.22/54.46         (r1_tarski @ (k10_relat_1 @ (sk_C_2 @ X1 @ X0) @ X2) @ X0)),
% 54.22/54.46      inference('demod', [status(thm)], ['39', '40'])).
% 54.22/54.46  thf('42', plain, (![X17 : $i]: (r1_tarski @ k1_xboole_0 @ X17)),
% 54.22/54.46      inference('cnf', [status(esa)], [t2_xboole_1])).
% 54.22/54.46  thf(d10_xboole_0, axiom,
% 54.22/54.46    (![A:$i,B:$i]:
% 54.22/54.46     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 54.22/54.46  thf('43', plain,
% 54.22/54.46      (![X10 : $i, X12 : $i]:
% 54.22/54.46         (((X10) = (X12))
% 54.22/54.46          | ~ (r1_tarski @ X12 @ X10)
% 54.22/54.46          | ~ (r1_tarski @ X10 @ X12))),
% 54.22/54.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 54.22/54.46  thf('44', plain,
% 54.22/54.46      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 54.22/54.46      inference('sup-', [status(thm)], ['42', '43'])).
% 54.22/54.46  thf('45', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i]:
% 54.22/54.46         ((k10_relat_1 @ (sk_C_2 @ X1 @ k1_xboole_0) @ X0) = (k1_xboole_0))),
% 54.22/54.46      inference('sup-', [status(thm)], ['41', '44'])).
% 54.22/54.46  thf(t145_funct_1, axiom,
% 54.22/54.46    (![A:$i,B:$i]:
% 54.22/54.46     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 54.22/54.46       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 54.22/54.46  thf('46', plain,
% 54.22/54.46      (![X68 : $i, X69 : $i]:
% 54.22/54.46         ((r1_tarski @ (k9_relat_1 @ X68 @ (k10_relat_1 @ X68 @ X69)) @ X69)
% 54.22/54.46          | ~ (v1_funct_1 @ X68)
% 54.22/54.46          | ~ (v1_relat_1 @ X68))),
% 54.22/54.46      inference('cnf', [status(esa)], [t145_funct_1])).
% 54.22/54.46  thf('47', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i]:
% 54.22/54.46         ((r1_tarski @ 
% 54.22/54.46           (k9_relat_1 @ (sk_C_2 @ X1 @ k1_xboole_0) @ k1_xboole_0) @ X0)
% 54.22/54.46          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ k1_xboole_0))
% 54.22/54.46          | ~ (v1_funct_1 @ (sk_C_2 @ X1 @ k1_xboole_0)))),
% 54.22/54.46      inference('sup+', [status(thm)], ['45', '46'])).
% 54.22/54.46  thf('48', plain,
% 54.22/54.46      (![X65 : $i, X66 : $i]: (v1_relat_1 @ (sk_C_2 @ X65 @ X66))),
% 54.22/54.46      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 54.22/54.46  thf('49', plain,
% 54.22/54.46      (![X65 : $i, X66 : $i]: (v1_funct_1 @ (sk_C_2 @ X65 @ X66))),
% 54.22/54.46      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 54.22/54.46  thf('50', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i]:
% 54.22/54.46         (r1_tarski @ 
% 54.22/54.46          (k9_relat_1 @ (sk_C_2 @ X1 @ k1_xboole_0) @ k1_xboole_0) @ X0)),
% 54.22/54.46      inference('demod', [status(thm)], ['47', '48', '49'])).
% 54.22/54.46  thf('51', plain,
% 54.22/54.46      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 54.22/54.46      inference('sup-', [status(thm)], ['42', '43'])).
% 54.22/54.46  thf('52', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         ((k9_relat_1 @ (sk_C_2 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 54.22/54.46           = (k1_xboole_0))),
% 54.22/54.46      inference('sup-', [status(thm)], ['50', '51'])).
% 54.22/54.46  thf('53', plain,
% 54.22/54.46      (![X65 : $i, X66 : $i]: ((k1_relat_1 @ (sk_C_2 @ X65 @ X66)) = (X66))),
% 54.22/54.46      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 54.22/54.46  thf(t146_relat_1, axiom,
% 54.22/54.46    (![A:$i]:
% 54.22/54.46     ( ( v1_relat_1 @ A ) =>
% 54.22/54.46       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 54.22/54.46  thf('54', plain,
% 54.22/54.46      (![X49 : $i]:
% 54.22/54.46         (((k9_relat_1 @ X49 @ (k1_relat_1 @ X49)) = (k2_relat_1 @ X49))
% 54.22/54.46          | ~ (v1_relat_1 @ X49))),
% 54.22/54.46      inference('cnf', [status(esa)], [t146_relat_1])).
% 54.22/54.46  thf('55', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i]:
% 54.22/54.46         (((k9_relat_1 @ (sk_C_2 @ X1 @ X0) @ X0)
% 54.22/54.46            = (k2_relat_1 @ (sk_C_2 @ X1 @ X0)))
% 54.22/54.46          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0)))),
% 54.22/54.46      inference('sup+', [status(thm)], ['53', '54'])).
% 54.22/54.46  thf('56', plain,
% 54.22/54.46      (![X65 : $i, X66 : $i]: (v1_relat_1 @ (sk_C_2 @ X65 @ X66))),
% 54.22/54.46      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 54.22/54.46  thf('57', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i]:
% 54.22/54.46         ((k9_relat_1 @ (sk_C_2 @ X1 @ X0) @ X0)
% 54.22/54.46           = (k2_relat_1 @ (sk_C_2 @ X1 @ X0)))),
% 54.22/54.46      inference('demod', [status(thm)], ['55', '56'])).
% 54.22/54.46  thf('58', plain,
% 54.22/54.46      (![X0 : $i]: ((k2_relat_1 @ (sk_C_2 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 54.22/54.46      inference('demod', [status(thm)], ['52', '57'])).
% 54.22/54.46  thf('59', plain,
% 54.22/54.46      (![X47 : $i, X48 : $i]:
% 54.22/54.46         ((r1_tarski @ (k9_relat_1 @ X47 @ X48) @ (k2_relat_1 @ X47))
% 54.22/54.46          | ~ (v1_relat_1 @ X47))),
% 54.22/54.46      inference('cnf', [status(esa)], [t144_relat_1])).
% 54.22/54.46  thf('60', plain,
% 54.22/54.46      (![X10 : $i, X12 : $i]:
% 54.22/54.46         (((X10) = (X12))
% 54.22/54.46          | ~ (r1_tarski @ X12 @ X10)
% 54.22/54.46          | ~ (r1_tarski @ X10 @ X12))),
% 54.22/54.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 54.22/54.46  thf('61', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i]:
% 54.22/54.46         (~ (v1_relat_1 @ X0)
% 54.22/54.46          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ (k9_relat_1 @ X0 @ X1))
% 54.22/54.46          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ X1)))),
% 54.22/54.46      inference('sup-', [status(thm)], ['59', '60'])).
% 54.22/54.46  thf('62', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i]:
% 54.22/54.46         (~ (r1_tarski @ k1_xboole_0 @ 
% 54.22/54.46             (k9_relat_1 @ (sk_C_2 @ X1 @ k1_xboole_0) @ X0))
% 54.22/54.46          | ((k2_relat_1 @ (sk_C_2 @ X1 @ k1_xboole_0))
% 54.22/54.46              = (k9_relat_1 @ (sk_C_2 @ X1 @ k1_xboole_0) @ X0))
% 54.22/54.46          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ k1_xboole_0)))),
% 54.22/54.46      inference('sup-', [status(thm)], ['58', '61'])).
% 54.22/54.46  thf('63', plain, (![X17 : $i]: (r1_tarski @ k1_xboole_0 @ X17)),
% 54.22/54.46      inference('cnf', [status(esa)], [t2_xboole_1])).
% 54.22/54.46  thf('64', plain,
% 54.22/54.46      (![X0 : $i]: ((k2_relat_1 @ (sk_C_2 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 54.22/54.46      inference('demod', [status(thm)], ['52', '57'])).
% 54.22/54.46  thf('65', plain,
% 54.22/54.46      (![X65 : $i, X66 : $i]: (v1_relat_1 @ (sk_C_2 @ X65 @ X66))),
% 54.22/54.46      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 54.22/54.46  thf('66', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i]:
% 54.22/54.46         ((k1_xboole_0) = (k9_relat_1 @ (sk_C_2 @ X1 @ k1_xboole_0) @ X0))),
% 54.22/54.46      inference('demod', [status(thm)], ['62', '63', '64', '65'])).
% 54.22/54.46  thf(t151_relat_1, axiom,
% 54.22/54.46    (![A:$i,B:$i]:
% 54.22/54.46     ( ( v1_relat_1 @ B ) =>
% 54.22/54.46       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 54.22/54.46         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 54.22/54.46  thf('67', plain,
% 54.22/54.46      (![X50 : $i, X51 : $i]:
% 54.22/54.46         (((k9_relat_1 @ X50 @ X51) != (k1_xboole_0))
% 54.22/54.46          | (r1_xboole_0 @ (k1_relat_1 @ X50) @ X51)
% 54.22/54.46          | ~ (v1_relat_1 @ X50))),
% 54.22/54.46      inference('cnf', [status(esa)], [t151_relat_1])).
% 54.22/54.46  thf('68', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i]:
% 54.22/54.46         (((k1_xboole_0) != (k1_xboole_0))
% 54.22/54.46          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ k1_xboole_0))
% 54.22/54.46          | (r1_xboole_0 @ (k1_relat_1 @ (sk_C_2 @ X1 @ k1_xboole_0)) @ X0))),
% 54.22/54.46      inference('sup-', [status(thm)], ['66', '67'])).
% 54.22/54.46  thf('69', plain,
% 54.22/54.46      (![X65 : $i, X66 : $i]: (v1_relat_1 @ (sk_C_2 @ X65 @ X66))),
% 54.22/54.46      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 54.22/54.46  thf('70', plain,
% 54.22/54.46      (![X65 : $i, X66 : $i]: ((k1_relat_1 @ (sk_C_2 @ X65 @ X66)) = (X66))),
% 54.22/54.46      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 54.22/54.46  thf('71', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 54.22/54.46      inference('demod', [status(thm)], ['68', '69', '70'])).
% 54.22/54.46  thf('72', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 54.22/54.46      inference('simplify', [status(thm)], ['71'])).
% 54.22/54.46  thf('73', plain,
% 54.22/54.46      (![X65 : $i, X66 : $i]: ((k1_relat_1 @ (sk_C_2 @ X65 @ X66)) = (X66))),
% 54.22/54.46      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 54.22/54.46  thf('74', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         (~ (v1_relat_1 @ X0)
% 54.22/54.46          | ((k1_xboole_0)
% 54.22/54.46              = (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ X0) @ k1_xboole_0))))),
% 54.22/54.46      inference('simplify', [status(thm)], ['28'])).
% 54.22/54.46  thf('75', plain,
% 54.22/54.46      (![X6 : $i, X8 : $i, X9 : $i]:
% 54.22/54.46         (~ (r2_hidden @ X8 @ (k3_xboole_0 @ X6 @ X9))
% 54.22/54.46          | ~ (r1_xboole_0 @ X6 @ X9))),
% 54.22/54.46      inference('cnf', [status(esa)], [t4_xboole_0])).
% 54.22/54.46  thf('76', plain,
% 54.22/54.46      (![X45 : $i, X46 : $i]:
% 54.22/54.46         ((k1_setfam_1 @ (k2_tarski @ X45 @ X46)) = (k3_xboole_0 @ X45 @ X46))),
% 54.22/54.46      inference('cnf', [status(esa)], [t12_setfam_1])).
% 54.22/54.46  thf('77', plain,
% 54.22/54.46      (![X6 : $i, X8 : $i, X9 : $i]:
% 54.22/54.46         (~ (r2_hidden @ X8 @ (k1_setfam_1 @ (k2_tarski @ X6 @ X9)))
% 54.22/54.46          | ~ (r1_xboole_0 @ X6 @ X9))),
% 54.22/54.46      inference('demod', [status(thm)], ['75', '76'])).
% 54.22/54.46  thf('78', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i]:
% 54.22/54.46         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 54.22/54.46          | ~ (v1_relat_1 @ X0)
% 54.22/54.46          | ~ (r1_xboole_0 @ (k1_relat_1 @ X0) @ k1_xboole_0))),
% 54.22/54.46      inference('sup-', [status(thm)], ['74', '77'])).
% 54.22/54.46  thf('79', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.22/54.46         (~ (r1_xboole_0 @ X0 @ k1_xboole_0)
% 54.22/54.46          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0))
% 54.22/54.46          | ~ (r2_hidden @ X2 @ k1_xboole_0))),
% 54.22/54.46      inference('sup-', [status(thm)], ['73', '78'])).
% 54.22/54.46  thf('80', plain,
% 54.22/54.46      (![X65 : $i, X66 : $i]: (v1_relat_1 @ (sk_C_2 @ X65 @ X66))),
% 54.22/54.46      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 54.22/54.46  thf('81', plain,
% 54.22/54.46      (![X0 : $i, X2 : $i]:
% 54.22/54.46         (~ (r1_xboole_0 @ X0 @ k1_xboole_0) | ~ (r2_hidden @ X2 @ k1_xboole_0))),
% 54.22/54.46      inference('demod', [status(thm)], ['79', '80'])).
% 54.22/54.46  thf('82', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 54.22/54.46      inference('sup-', [status(thm)], ['72', '81'])).
% 54.22/54.46  thf('83', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 54.22/54.46      inference('clc', [status(thm)], ['36', '82'])).
% 54.22/54.46  thf('84', plain,
% 54.22/54.46      (![X50 : $i, X51 : $i]:
% 54.22/54.46         (~ (r1_xboole_0 @ (k1_relat_1 @ X50) @ X51)
% 54.22/54.46          | ((k9_relat_1 @ X50 @ X51) = (k1_xboole_0))
% 54.22/54.46          | ~ (v1_relat_1 @ X50))),
% 54.22/54.46      inference('cnf', [status(esa)], [t151_relat_1])).
% 54.22/54.46  thf('85', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         (~ (v1_relat_1 @ X0)
% 54.22/54.46          | ((k9_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 54.22/54.46      inference('sup-', [status(thm)], ['83', '84'])).
% 54.22/54.46  thf('86', plain,
% 54.22/54.46      (![X74 : $i, X75 : $i]:
% 54.22/54.46         (~ (v2_funct_1 @ X74)
% 54.22/54.46          | ((k10_relat_1 @ X74 @ X75)
% 54.22/54.46              = (k9_relat_1 @ (k2_funct_1 @ X74) @ X75))
% 54.22/54.46          | ~ (v1_funct_1 @ X74)
% 54.22/54.46          | ~ (v1_relat_1 @ X74))),
% 54.22/54.46      inference('cnf', [status(esa)], [t155_funct_1])).
% 54.22/54.46  thf('87', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         (((k10_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 54.22/54.46          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 54.22/54.46          | ~ (v1_relat_1 @ X0)
% 54.22/54.46          | ~ (v1_funct_1 @ X0)
% 54.22/54.46          | ~ (v2_funct_1 @ X0))),
% 54.22/54.46      inference('sup+', [status(thm)], ['85', '86'])).
% 54.22/54.46  thf('88', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         (~ (v1_relat_1 @ X0)
% 54.22/54.46          | ~ (v1_funct_1 @ X0)
% 54.22/54.46          | ~ (v2_funct_1 @ X0)
% 54.22/54.46          | ~ (v1_funct_1 @ X0)
% 54.22/54.46          | ~ (v1_relat_1 @ X0)
% 54.22/54.46          | ((k10_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 54.22/54.46      inference('sup-', [status(thm)], ['20', '87'])).
% 54.22/54.46  thf('89', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         (((k10_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 54.22/54.46          | ~ (v2_funct_1 @ X0)
% 54.22/54.46          | ~ (v1_funct_1 @ X0)
% 54.22/54.46          | ~ (v1_relat_1 @ X0))),
% 54.22/54.46      inference('simplify', [status(thm)], ['88'])).
% 54.22/54.46  thf('90', plain,
% 54.22/54.46      (![X55 : $i, X56 : $i]:
% 54.22/54.46         ((r1_tarski @ (k10_relat_1 @ X55 @ X56) @ (k1_relat_1 @ X55))
% 54.22/54.46          | ~ (v1_relat_1 @ X55))),
% 54.22/54.46      inference('cnf', [status(esa)], [t167_relat_1])).
% 54.22/54.46  thf('91', plain,
% 54.22/54.46      (![X62 : $i, X63 : $i]:
% 54.22/54.46         (~ (r1_tarski @ X62 @ (k1_relat_1 @ X63))
% 54.22/54.46          | ((k1_relat_1 @ (k7_relat_1 @ X63 @ X62)) = (X62))
% 54.22/54.46          | ~ (v1_relat_1 @ X63))),
% 54.22/54.46      inference('cnf', [status(esa)], [t91_relat_1])).
% 54.22/54.46  thf('92', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i]:
% 54.22/54.46         (~ (v1_relat_1 @ X0)
% 54.22/54.46          | ~ (v1_relat_1 @ X0)
% 54.22/54.46          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1)))
% 54.22/54.46              = (k10_relat_1 @ X0 @ X1)))),
% 54.22/54.46      inference('sup-', [status(thm)], ['90', '91'])).
% 54.22/54.46  thf('93', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i]:
% 54.22/54.46         (((k1_relat_1 @ (k7_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1)))
% 54.22/54.46            = (k10_relat_1 @ X0 @ X1))
% 54.22/54.46          | ~ (v1_relat_1 @ X0))),
% 54.22/54.46      inference('simplify', [status(thm)], ['92'])).
% 54.22/54.46  thf('94', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         (((k1_relat_1 @ (k7_relat_1 @ X0 @ k1_xboole_0))
% 54.22/54.46            = (k10_relat_1 @ X0 @ k1_xboole_0))
% 54.22/54.46          | ~ (v1_relat_1 @ X0)
% 54.22/54.46          | ~ (v1_funct_1 @ X0)
% 54.22/54.46          | ~ (v2_funct_1 @ X0)
% 54.22/54.46          | ~ (v1_relat_1 @ X0))),
% 54.22/54.46      inference('sup+', [status(thm)], ['89', '93'])).
% 54.22/54.46  thf('95', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         (~ (v2_funct_1 @ X0)
% 54.22/54.46          | ~ (v1_funct_1 @ X0)
% 54.22/54.46          | ~ (v1_relat_1 @ X0)
% 54.22/54.46          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ k1_xboole_0))
% 54.22/54.46              = (k10_relat_1 @ X0 @ k1_xboole_0)))),
% 54.22/54.46      inference('simplify', [status(thm)], ['94'])).
% 54.22/54.46  thf('96', plain,
% 54.22/54.46      (![X65 : $i, X66 : $i]: ((k1_relat_1 @ (sk_C_2 @ X65 @ X66)) = (X66))),
% 54.22/54.46      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 54.22/54.46  thf('97', plain,
% 54.22/54.46      (![X68 : $i, X69 : $i]:
% 54.22/54.46         ((r1_tarski @ (k9_relat_1 @ X68 @ (k10_relat_1 @ X68 @ X69)) @ X69)
% 54.22/54.46          | ~ (v1_funct_1 @ X68)
% 54.22/54.46          | ~ (v1_relat_1 @ X68))),
% 54.22/54.46      inference('cnf', [status(esa)], [t145_funct_1])).
% 54.22/54.46  thf('98', plain,
% 54.22/54.46      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 54.22/54.46      inference('sup-', [status(thm)], ['42', '43'])).
% 54.22/54.46  thf('99', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         (~ (v1_relat_1 @ X0)
% 54.22/54.46          | ~ (v1_funct_1 @ X0)
% 54.22/54.46          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ k1_xboole_0))
% 54.22/54.46              = (k1_xboole_0)))),
% 54.22/54.46      inference('sup-', [status(thm)], ['97', '98'])).
% 54.22/54.46  thf('100', plain,
% 54.22/54.46      (![X50 : $i, X51 : $i]:
% 54.22/54.46         (((k9_relat_1 @ X50 @ X51) != (k1_xboole_0))
% 54.22/54.46          | (r1_xboole_0 @ (k1_relat_1 @ X50) @ X51)
% 54.22/54.46          | ~ (v1_relat_1 @ X50))),
% 54.22/54.46      inference('cnf', [status(esa)], [t151_relat_1])).
% 54.22/54.46  thf('101', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         (((k1_xboole_0) != (k1_xboole_0))
% 54.22/54.46          | ~ (v1_funct_1 @ X0)
% 54.22/54.46          | ~ (v1_relat_1 @ X0)
% 54.22/54.46          | ~ (v1_relat_1 @ X0)
% 54.22/54.46          | (r1_xboole_0 @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ k1_xboole_0)))),
% 54.22/54.46      inference('sup-', [status(thm)], ['99', '100'])).
% 54.22/54.46  thf('102', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         ((r1_xboole_0 @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ k1_xboole_0))
% 54.22/54.46          | ~ (v1_relat_1 @ X0)
% 54.22/54.46          | ~ (v1_funct_1 @ X0))),
% 54.22/54.46      inference('simplify', [status(thm)], ['101'])).
% 54.22/54.46  thf('103', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i]:
% 54.22/54.46         ((r1_xboole_0 @ X0 @ (k10_relat_1 @ (sk_C_2 @ X1 @ X0) @ k1_xboole_0))
% 54.22/54.46          | ~ (v1_funct_1 @ (sk_C_2 @ X1 @ X0))
% 54.22/54.46          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0)))),
% 54.22/54.46      inference('sup+', [status(thm)], ['96', '102'])).
% 54.22/54.46  thf('104', plain,
% 54.22/54.46      (![X65 : $i, X66 : $i]: (v1_funct_1 @ (sk_C_2 @ X65 @ X66))),
% 54.22/54.46      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 54.22/54.46  thf('105', plain,
% 54.22/54.46      (![X65 : $i, X66 : $i]: (v1_relat_1 @ (sk_C_2 @ X65 @ X66))),
% 54.22/54.46      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 54.22/54.46  thf('106', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i]:
% 54.22/54.46         (r1_xboole_0 @ X0 @ (k10_relat_1 @ (sk_C_2 @ X1 @ X0) @ k1_xboole_0))),
% 54.22/54.46      inference('demod', [status(thm)], ['103', '104', '105'])).
% 54.22/54.46  thf(d3_tarski, axiom,
% 54.22/54.46    (![A:$i,B:$i]:
% 54.22/54.46     ( ( r1_tarski @ A @ B ) <=>
% 54.22/54.46       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 54.22/54.46  thf('107', plain,
% 54.22/54.46      (![X3 : $i, X5 : $i]:
% 54.22/54.46         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 54.22/54.46      inference('cnf', [status(esa)], [d3_tarski])).
% 54.22/54.46  thf('108', plain,
% 54.22/54.46      (![X6 : $i, X8 : $i, X9 : $i]:
% 54.22/54.46         (~ (r2_hidden @ X8 @ (k1_setfam_1 @ (k2_tarski @ X6 @ X9)))
% 54.22/54.46          | ~ (r1_xboole_0 @ X6 @ X9))),
% 54.22/54.46      inference('demod', [status(thm)], ['75', '76'])).
% 54.22/54.46  thf('109', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.22/54.46         ((r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X2)
% 54.22/54.46          | ~ (r1_xboole_0 @ X1 @ X0))),
% 54.22/54.46      inference('sup-', [status(thm)], ['107', '108'])).
% 54.22/54.46  thf('110', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.22/54.46         (r1_tarski @ 
% 54.22/54.46          (k1_setfam_1 @ 
% 54.22/54.46           (k2_tarski @ X0 @ (k10_relat_1 @ (sk_C_2 @ X1 @ X0) @ k1_xboole_0))) @ 
% 54.22/54.46          X2)),
% 54.22/54.46      inference('sup-', [status(thm)], ['106', '109'])).
% 54.22/54.46  thf('111', plain,
% 54.22/54.46      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 54.22/54.46      inference('sup-', [status(thm)], ['42', '43'])).
% 54.22/54.46  thf('112', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i]:
% 54.22/54.46         ((k1_setfam_1 @ 
% 54.22/54.46           (k2_tarski @ X0 @ (k10_relat_1 @ (sk_C_2 @ X1 @ X0) @ k1_xboole_0)))
% 54.22/54.46           = (k1_xboole_0))),
% 54.22/54.46      inference('sup-', [status(thm)], ['110', '111'])).
% 54.22/54.46  thf('113', plain,
% 54.22/54.46      (![X65 : $i, X66 : $i]: ((k1_relat_1 @ (sk_C_2 @ X65 @ X66)) = (X66))),
% 54.22/54.46      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 54.22/54.46  thf('114', plain,
% 54.22/54.46      (![X60 : $i, X61 : $i]:
% 54.22/54.46         (((k1_relat_1 @ (k7_relat_1 @ X60 @ X61))
% 54.22/54.46            = (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ X60) @ X61)))
% 54.22/54.46          | ~ (v1_relat_1 @ X60))),
% 54.22/54.46      inference('demod', [status(thm)], ['25', '26'])).
% 54.22/54.46  thf('115', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i]:
% 54.22/54.46         (((k1_relat_1 @ (k7_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1)))
% 54.22/54.46            = (k10_relat_1 @ X0 @ X1))
% 54.22/54.46          | ~ (v1_relat_1 @ X0))),
% 54.22/54.46      inference('simplify', [status(thm)], ['92'])).
% 54.22/54.46  thf('116', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i]:
% 54.22/54.46         (((k1_setfam_1 @ 
% 54.22/54.46            (k2_tarski @ (k1_relat_1 @ X1) @ (k10_relat_1 @ X1 @ X0)))
% 54.22/54.46            = (k10_relat_1 @ X1 @ X0))
% 54.22/54.46          | ~ (v1_relat_1 @ X1)
% 54.22/54.46          | ~ (v1_relat_1 @ X1))),
% 54.22/54.46      inference('sup+', [status(thm)], ['114', '115'])).
% 54.22/54.46  thf('117', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i]:
% 54.22/54.46         (~ (v1_relat_1 @ X1)
% 54.22/54.46          | ((k1_setfam_1 @ 
% 54.22/54.46              (k2_tarski @ (k1_relat_1 @ X1) @ (k10_relat_1 @ X1 @ X0)))
% 54.22/54.46              = (k10_relat_1 @ X1 @ X0)))),
% 54.22/54.46      inference('simplify', [status(thm)], ['116'])).
% 54.22/54.46  thf('118', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.22/54.46         (((k1_setfam_1 @ 
% 54.22/54.46            (k2_tarski @ X0 @ (k10_relat_1 @ (sk_C_2 @ X2 @ X0) @ X1)))
% 54.22/54.46            = (k10_relat_1 @ (sk_C_2 @ X2 @ X0) @ X1))
% 54.22/54.46          | ~ (v1_relat_1 @ (sk_C_2 @ X2 @ X0)))),
% 54.22/54.46      inference('sup+', [status(thm)], ['113', '117'])).
% 54.22/54.46  thf('119', plain,
% 54.22/54.46      (![X65 : $i, X66 : $i]: (v1_relat_1 @ (sk_C_2 @ X65 @ X66))),
% 54.22/54.46      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 54.22/54.46  thf('120', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.22/54.46         ((k1_setfam_1 @ 
% 54.22/54.46           (k2_tarski @ X0 @ (k10_relat_1 @ (sk_C_2 @ X2 @ X0) @ X1)))
% 54.22/54.46           = (k10_relat_1 @ (sk_C_2 @ X2 @ X0) @ X1))),
% 54.22/54.46      inference('demod', [status(thm)], ['118', '119'])).
% 54.22/54.46  thf('121', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i]:
% 54.22/54.46         ((k10_relat_1 @ (sk_C_2 @ X1 @ X0) @ k1_xboole_0) = (k1_xboole_0))),
% 54.22/54.46      inference('demod', [status(thm)], ['112', '120'])).
% 54.22/54.46  thf('122', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('123', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.22/54.46         (r1_tarski @ (k10_relat_1 @ (sk_C_2 @ X1 @ X0) @ X2) @ X0)),
% 54.22/54.46      inference('demod', [status(thm)], ['39', '40'])).
% 54.22/54.46  thf('124', plain,
% 54.22/54.46      (![X14 : $i, X15 : $i, X16 : $i]:
% 54.22/54.46         (~ (r1_tarski @ X14 @ X15)
% 54.22/54.46          | ~ (r1_tarski @ X15 @ X16)
% 54.22/54.46          | (r1_tarski @ X14 @ X16))),
% 54.22/54.46      inference('cnf', [status(esa)], [t1_xboole_1])).
% 54.22/54.46  thf('125', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 54.22/54.46         ((r1_tarski @ (k10_relat_1 @ (sk_C_2 @ X2 @ X0) @ X1) @ X3)
% 54.22/54.46          | ~ (r1_tarski @ X0 @ X3))),
% 54.22/54.46      inference('sup-', [status(thm)], ['123', '124'])).
% 54.22/54.46  thf('126', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i]:
% 54.22/54.46         (r1_tarski @ (k10_relat_1 @ (sk_C_2 @ X1 @ sk_A) @ X0) @ 
% 54.22/54.46          (k1_relat_1 @ sk_B))),
% 54.22/54.46      inference('sup-', [status(thm)], ['122', '125'])).
% 54.22/54.46  thf('127', plain,
% 54.22/54.46      (![X62 : $i, X63 : $i]:
% 54.22/54.46         (~ (r1_tarski @ X62 @ (k1_relat_1 @ X63))
% 54.22/54.46          | ((k1_relat_1 @ (k7_relat_1 @ X63 @ X62)) = (X62))
% 54.22/54.46          | ~ (v1_relat_1 @ X63))),
% 54.22/54.46      inference('cnf', [status(esa)], [t91_relat_1])).
% 54.22/54.46  thf('128', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i]:
% 54.22/54.46         (~ (v1_relat_1 @ sk_B)
% 54.22/54.46          | ((k1_relat_1 @ 
% 54.22/54.46              (k7_relat_1 @ sk_B @ (k10_relat_1 @ (sk_C_2 @ X1 @ sk_A) @ X0)))
% 54.22/54.46              = (k10_relat_1 @ (sk_C_2 @ X1 @ sk_A) @ X0)))),
% 54.22/54.46      inference('sup-', [status(thm)], ['126', '127'])).
% 54.22/54.46  thf('129', plain, ((v1_relat_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('130', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i]:
% 54.22/54.46         ((k1_relat_1 @ 
% 54.22/54.46           (k7_relat_1 @ sk_B @ (k10_relat_1 @ (sk_C_2 @ X1 @ sk_A) @ X0)))
% 54.22/54.46           = (k10_relat_1 @ (sk_C_2 @ X1 @ sk_A) @ X0))),
% 54.22/54.46      inference('demod', [status(thm)], ['128', '129'])).
% 54.22/54.46  thf('131', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         ((k1_relat_1 @ (k7_relat_1 @ sk_B @ k1_xboole_0))
% 54.22/54.46           = (k10_relat_1 @ (sk_C_2 @ X0 @ sk_A) @ k1_xboole_0))),
% 54.22/54.46      inference('sup+', [status(thm)], ['121', '130'])).
% 54.22/54.46  thf('132', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i]:
% 54.22/54.46         ((k10_relat_1 @ (sk_C_2 @ X1 @ X0) @ k1_xboole_0) = (k1_xboole_0))),
% 54.22/54.46      inference('demod', [status(thm)], ['112', '120'])).
% 54.22/54.46  thf('133', plain,
% 54.22/54.46      (((k1_relat_1 @ (k7_relat_1 @ sk_B @ k1_xboole_0)) = (k1_xboole_0))),
% 54.22/54.46      inference('demod', [status(thm)], ['131', '132'])).
% 54.22/54.46  thf('134', plain,
% 54.22/54.46      ((((k10_relat_1 @ sk_B @ k1_xboole_0) = (k1_xboole_0))
% 54.22/54.46        | ~ (v1_relat_1 @ sk_B)
% 54.22/54.46        | ~ (v1_funct_1 @ sk_B)
% 54.22/54.46        | ~ (v2_funct_1 @ sk_B))),
% 54.22/54.46      inference('sup+', [status(thm)], ['95', '133'])).
% 54.22/54.46  thf('135', plain, ((v1_relat_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('136', plain, ((v1_funct_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('137', plain, ((v2_funct_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('138', plain, (((k10_relat_1 @ sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 54.22/54.46      inference('demod', [status(thm)], ['134', '135', '136', '137'])).
% 54.22/54.46  thf('139', plain,
% 54.22/54.46      (![X68 : $i, X69 : $i]:
% 54.22/54.46         ((r1_tarski @ (k9_relat_1 @ X68 @ (k10_relat_1 @ X68 @ X69)) @ X69)
% 54.22/54.46          | ~ (v1_funct_1 @ X68)
% 54.22/54.46          | ~ (v1_relat_1 @ X68))),
% 54.22/54.46      inference('cnf', [status(esa)], [t145_funct_1])).
% 54.22/54.46  thf('140', plain,
% 54.22/54.46      (![X10 : $i, X12 : $i]:
% 54.22/54.46         (((X10) = (X12))
% 54.22/54.46          | ~ (r1_tarski @ X12 @ X10)
% 54.22/54.46          | ~ (r1_tarski @ X10 @ X12))),
% 54.22/54.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 54.22/54.46  thf('141', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i]:
% 54.22/54.46         (~ (v1_relat_1 @ X1)
% 54.22/54.46          | ~ (v1_funct_1 @ X1)
% 54.22/54.46          | ~ (r1_tarski @ X0 @ (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0)))
% 54.22/54.46          | ((X0) = (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0))))),
% 54.22/54.46      inference('sup-', [status(thm)], ['139', '140'])).
% 54.22/54.46  thf('142', plain,
% 54.22/54.46      ((~ (r1_tarski @ k1_xboole_0 @ (k9_relat_1 @ sk_B @ k1_xboole_0))
% 54.22/54.46        | ((k1_xboole_0)
% 54.22/54.46            = (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ k1_xboole_0)))
% 54.22/54.46        | ~ (v1_funct_1 @ sk_B)
% 54.22/54.46        | ~ (v1_relat_1 @ sk_B))),
% 54.22/54.46      inference('sup-', [status(thm)], ['138', '141'])).
% 54.22/54.46  thf('143', plain, (![X17 : $i]: (r1_tarski @ k1_xboole_0 @ X17)),
% 54.22/54.46      inference('cnf', [status(esa)], [t2_xboole_1])).
% 54.22/54.46  thf('144', plain, (((k10_relat_1 @ sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 54.22/54.46      inference('demod', [status(thm)], ['134', '135', '136', '137'])).
% 54.22/54.46  thf('145', plain, ((v1_funct_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('146', plain, ((v1_relat_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('147', plain, (((k1_xboole_0) = (k9_relat_1 @ sk_B @ k1_xboole_0))),
% 54.22/54.46      inference('demod', [status(thm)], ['142', '143', '144', '145', '146'])).
% 54.22/54.46  thf('148', plain,
% 54.22/54.46      (![X49 : $i]:
% 54.22/54.46         (((k9_relat_1 @ X49 @ (k1_relat_1 @ X49)) = (k2_relat_1 @ X49))
% 54.22/54.46          | ~ (v1_relat_1 @ X49))),
% 54.22/54.46      inference('cnf', [status(esa)], [t146_relat_1])).
% 54.22/54.46  thf(t153_relat_1, axiom,
% 54.22/54.46    (![A:$i,B:$i,C:$i]:
% 54.22/54.46     ( ( v1_relat_1 @ C ) =>
% 54.22/54.46       ( ( k9_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 54.22/54.46         ( k2_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 54.22/54.46  thf('149', plain,
% 54.22/54.46      (![X52 : $i, X53 : $i, X54 : $i]:
% 54.22/54.46         (((k9_relat_1 @ X52 @ (k2_xboole_0 @ X53 @ X54))
% 54.22/54.46            = (k2_xboole_0 @ (k9_relat_1 @ X52 @ X53) @ 
% 54.22/54.46               (k9_relat_1 @ X52 @ X54)))
% 54.22/54.46          | ~ (v1_relat_1 @ X52))),
% 54.22/54.46      inference('cnf', [status(esa)], [t153_relat_1])).
% 54.22/54.46  thf('150', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i]:
% 54.22/54.46         (((k9_relat_1 @ X0 @ (k2_xboole_0 @ (k1_relat_1 @ X0) @ X1))
% 54.22/54.46            = (k2_xboole_0 @ (k2_relat_1 @ X0) @ (k9_relat_1 @ X0 @ X1)))
% 54.22/54.46          | ~ (v1_relat_1 @ X0)
% 54.22/54.46          | ~ (v1_relat_1 @ X0))),
% 54.22/54.46      inference('sup+', [status(thm)], ['148', '149'])).
% 54.22/54.46  thf('151', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i]:
% 54.22/54.46         (~ (v1_relat_1 @ X0)
% 54.22/54.46          | ((k9_relat_1 @ X0 @ (k2_xboole_0 @ (k1_relat_1 @ X0) @ X1))
% 54.22/54.46              = (k2_xboole_0 @ (k2_relat_1 @ X0) @ (k9_relat_1 @ X0 @ X1))))),
% 54.22/54.46      inference('simplify', [status(thm)], ['150'])).
% 54.22/54.46  thf('152', plain,
% 54.22/54.46      ((((k9_relat_1 @ sk_B @ (k2_xboole_0 @ (k1_relat_1 @ sk_B) @ k1_xboole_0))
% 54.22/54.46          = (k2_xboole_0 @ (k2_relat_1 @ sk_B) @ k1_xboole_0))
% 54.22/54.46        | ~ (v1_relat_1 @ sk_B))),
% 54.22/54.46      inference('sup+', [status(thm)], ['147', '151'])).
% 54.22/54.46  thf(commutativity_k2_xboole_0, axiom,
% 54.22/54.46    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 54.22/54.46  thf('153', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 54.22/54.46      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 54.22/54.46  thf('154', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 54.22/54.46      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 54.22/54.46  thf(t1_boole, axiom,
% 54.22/54.46    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 54.22/54.46  thf('155', plain, (![X13 : $i]: ((k2_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 54.22/54.46      inference('cnf', [status(esa)], [t1_boole])).
% 54.22/54.46  thf('156', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 54.22/54.46      inference('sup+', [status(thm)], ['154', '155'])).
% 54.22/54.46  thf('157', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 54.22/54.46      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 54.22/54.46  thf('158', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 54.22/54.46      inference('sup+', [status(thm)], ['154', '155'])).
% 54.22/54.46  thf('159', plain, ((v1_relat_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('160', plain,
% 54.22/54.46      (((k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)) = (k2_relat_1 @ sk_B))),
% 54.22/54.46      inference('demod', [status(thm)],
% 54.22/54.46                ['152', '153', '156', '157', '158', '159'])).
% 54.22/54.46  thf('161', plain,
% 54.22/54.46      (![X64 : $i]:
% 54.22/54.46         ((v1_relat_1 @ (k2_funct_1 @ X64))
% 54.22/54.46          | ~ (v1_funct_1 @ X64)
% 54.22/54.46          | ~ (v1_relat_1 @ X64))),
% 54.22/54.46      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 54.22/54.46  thf('162', plain,
% 54.22/54.46      (![X72 : $i, X73 : $i]:
% 54.22/54.46         (~ (v2_funct_1 @ X72)
% 54.22/54.46          | ((k9_relat_1 @ X72 @ X73)
% 54.22/54.46              = (k10_relat_1 @ (k2_funct_1 @ X72) @ X73))
% 54.22/54.46          | ~ (v1_funct_1 @ X72)
% 54.22/54.46          | ~ (v1_relat_1 @ X72))),
% 54.22/54.46      inference('cnf', [status(esa)], [t154_funct_1])).
% 54.22/54.46  thf('163', plain,
% 54.22/54.46      (![X55 : $i, X56 : $i]:
% 54.22/54.46         ((r1_tarski @ (k10_relat_1 @ X55 @ X56) @ (k1_relat_1 @ X55))
% 54.22/54.46          | ~ (v1_relat_1 @ X55))),
% 54.22/54.46      inference('cnf', [status(esa)], [t167_relat_1])).
% 54.22/54.46  thf('164', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i]:
% 54.22/54.46         ((r1_tarski @ (k9_relat_1 @ X1 @ X0) @ 
% 54.22/54.46           (k1_relat_1 @ (k2_funct_1 @ X1)))
% 54.22/54.46          | ~ (v1_relat_1 @ X1)
% 54.22/54.46          | ~ (v1_funct_1 @ X1)
% 54.22/54.46          | ~ (v2_funct_1 @ X1)
% 54.22/54.46          | ~ (v1_relat_1 @ (k2_funct_1 @ X1)))),
% 54.22/54.46      inference('sup+', [status(thm)], ['162', '163'])).
% 54.22/54.46  thf('165', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i]:
% 54.22/54.46         (~ (v1_relat_1 @ X0)
% 54.22/54.46          | ~ (v1_funct_1 @ X0)
% 54.22/54.46          | ~ (v2_funct_1 @ X0)
% 54.22/54.46          | ~ (v1_funct_1 @ X0)
% 54.22/54.46          | ~ (v1_relat_1 @ X0)
% 54.22/54.46          | (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ 
% 54.22/54.46             (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 54.22/54.46      inference('sup-', [status(thm)], ['161', '164'])).
% 54.22/54.46  thf('166', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i]:
% 54.22/54.46         ((r1_tarski @ (k9_relat_1 @ X0 @ X1) @ 
% 54.22/54.46           (k1_relat_1 @ (k2_funct_1 @ X0)))
% 54.22/54.46          | ~ (v2_funct_1 @ X0)
% 54.22/54.46          | ~ (v1_funct_1 @ X0)
% 54.22/54.46          | ~ (v1_relat_1 @ X0))),
% 54.22/54.46      inference('simplify', [status(thm)], ['165'])).
% 54.22/54.46  thf('167', plain,
% 54.22/54.46      (![X10 : $i, X12 : $i]:
% 54.22/54.46         (((X10) = (X12))
% 54.22/54.46          | ~ (r1_tarski @ X12 @ X10)
% 54.22/54.46          | ~ (r1_tarski @ X10 @ X12))),
% 54.22/54.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 54.22/54.46  thf('168', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i]:
% 54.22/54.46         (~ (v1_relat_1 @ X0)
% 54.22/54.46          | ~ (v1_funct_1 @ X0)
% 54.22/54.46          | ~ (v2_funct_1 @ X0)
% 54.22/54.46          | ~ (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 54.22/54.46               (k9_relat_1 @ X0 @ X1))
% 54.22/54.46          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k9_relat_1 @ X0 @ X1)))),
% 54.22/54.46      inference('sup-', [status(thm)], ['166', '167'])).
% 54.22/54.46  thf('169', plain,
% 54.22/54.46      ((~ (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_B)) @ (k2_relat_1 @ sk_B))
% 54.22/54.46        | ((k1_relat_1 @ (k2_funct_1 @ sk_B))
% 54.22/54.46            = (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)))
% 54.22/54.46        | ~ (v2_funct_1 @ sk_B)
% 54.22/54.46        | ~ (v1_funct_1 @ sk_B)
% 54.22/54.46        | ~ (v1_relat_1 @ sk_B))),
% 54.22/54.46      inference('sup-', [status(thm)], ['160', '168'])).
% 54.22/54.46  thf('170', plain,
% 54.22/54.46      (((k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)) = (k2_relat_1 @ sk_B))),
% 54.22/54.46      inference('demod', [status(thm)],
% 54.22/54.46                ['152', '153', '156', '157', '158', '159'])).
% 54.22/54.46  thf('171', plain, ((v2_funct_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('172', plain, ((v1_funct_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('173', plain, ((v1_relat_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('174', plain,
% 54.22/54.46      ((~ (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_B)) @ (k2_relat_1 @ sk_B))
% 54.22/54.46        | ((k1_relat_1 @ (k2_funct_1 @ sk_B)) = (k2_relat_1 @ sk_B)))),
% 54.22/54.46      inference('demod', [status(thm)], ['169', '170', '171', '172', '173'])).
% 54.22/54.46  thf('175', plain,
% 54.22/54.46      ((~ (v1_relat_1 @ sk_B)
% 54.22/54.46        | ~ (v1_funct_1 @ sk_B)
% 54.22/54.46        | ~ (v2_funct_1 @ sk_B)
% 54.22/54.46        | ((k1_relat_1 @ (k2_funct_1 @ sk_B)) = (k2_relat_1 @ sk_B)))),
% 54.22/54.46      inference('sup-', [status(thm)], ['19', '174'])).
% 54.22/54.46  thf('176', plain, ((v1_relat_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('177', plain, ((v1_funct_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('178', plain, ((v2_funct_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('179', plain,
% 54.22/54.46      (((k1_relat_1 @ (k2_funct_1 @ sk_B)) = (k2_relat_1 @ sk_B))),
% 54.22/54.46      inference('demod', [status(thm)], ['175', '176', '177', '178'])).
% 54.22/54.46  thf('180', plain,
% 54.22/54.46      (![X49 : $i]:
% 54.22/54.46         (((k9_relat_1 @ X49 @ (k1_relat_1 @ X49)) = (k2_relat_1 @ X49))
% 54.22/54.46          | ~ (v1_relat_1 @ X49))),
% 54.22/54.46      inference('cnf', [status(esa)], [t146_relat_1])).
% 54.22/54.46  thf('181', plain,
% 54.22/54.46      ((((k9_relat_1 @ (k2_funct_1 @ sk_B) @ (k2_relat_1 @ sk_B))
% 54.22/54.46          = (k2_relat_1 @ (k2_funct_1 @ sk_B)))
% 54.22/54.46        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 54.22/54.46      inference('sup+', [status(thm)], ['179', '180'])).
% 54.22/54.46  thf('182', plain,
% 54.22/54.46      ((~ (v1_relat_1 @ sk_B)
% 54.22/54.46        | ~ (v1_funct_1 @ sk_B)
% 54.22/54.46        | ((k9_relat_1 @ (k2_funct_1 @ sk_B) @ (k2_relat_1 @ sk_B))
% 54.22/54.46            = (k2_relat_1 @ (k2_funct_1 @ sk_B))))),
% 54.22/54.46      inference('sup-', [status(thm)], ['5', '181'])).
% 54.22/54.46  thf('183', plain, ((v1_relat_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('184', plain, ((v1_funct_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('185', plain,
% 54.22/54.46      (((k9_relat_1 @ (k2_funct_1 @ sk_B) @ (k2_relat_1 @ sk_B))
% 54.22/54.46         = (k2_relat_1 @ (k2_funct_1 @ sk_B)))),
% 54.22/54.46      inference('demod', [status(thm)], ['182', '183', '184'])).
% 54.22/54.46  thf('186', plain,
% 54.22/54.46      ((((k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))
% 54.22/54.46          = (k2_relat_1 @ (k2_funct_1 @ sk_B)))
% 54.22/54.46        | ~ (v1_relat_1 @ sk_B)
% 54.22/54.46        | ~ (v1_funct_1 @ sk_B)
% 54.22/54.46        | ~ (v2_funct_1 @ sk_B))),
% 54.22/54.46      inference('sup+', [status(thm)], ['4', '185'])).
% 54.22/54.46  thf('187', plain, ((v1_relat_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('188', plain, ((v1_funct_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('189', plain, ((v2_funct_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('190', plain,
% 54.22/54.46      (((k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))
% 54.22/54.46         = (k2_relat_1 @ (k2_funct_1 @ sk_B)))),
% 54.22/54.46      inference('demod', [status(thm)], ['186', '187', '188', '189'])).
% 54.22/54.46  thf('191', plain,
% 54.22/54.46      ((((k1_relat_1 @ sk_B) = (k2_relat_1 @ (k2_funct_1 @ sk_B)))
% 54.22/54.46        | ~ (v1_relat_1 @ sk_B))),
% 54.22/54.46      inference('sup+', [status(thm)], ['3', '190'])).
% 54.22/54.46  thf('192', plain, ((v1_relat_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('193', plain,
% 54.22/54.46      (((k1_relat_1 @ sk_B) = (k2_relat_1 @ (k2_funct_1 @ sk_B)))),
% 54.22/54.46      inference('demod', [status(thm)], ['191', '192'])).
% 54.22/54.46  thf(t147_funct_1, axiom,
% 54.22/54.46    (![A:$i,B:$i]:
% 54.22/54.46     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 54.22/54.46       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 54.22/54.46         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 54.22/54.46  thf('194', plain,
% 54.22/54.46      (![X70 : $i, X71 : $i]:
% 54.22/54.46         (~ (r1_tarski @ X70 @ (k2_relat_1 @ X71))
% 54.22/54.46          | ((k9_relat_1 @ X71 @ (k10_relat_1 @ X71 @ X70)) = (X70))
% 54.22/54.46          | ~ (v1_funct_1 @ X71)
% 54.22/54.46          | ~ (v1_relat_1 @ X71))),
% 54.22/54.46      inference('cnf', [status(esa)], [t147_funct_1])).
% 54.22/54.46  thf('195', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         (~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_B))
% 54.22/54.46          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 54.22/54.46          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 54.22/54.46          | ((k9_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 54.22/54.46              (k10_relat_1 @ (k2_funct_1 @ sk_B) @ X0)) = (X0)))),
% 54.22/54.46      inference('sup-', [status(thm)], ['193', '194'])).
% 54.22/54.46  thf('196', plain,
% 54.22/54.46      (![X72 : $i, X73 : $i]:
% 54.22/54.46         (~ (v2_funct_1 @ X72)
% 54.22/54.46          | ((k9_relat_1 @ X72 @ X73)
% 54.22/54.46              = (k10_relat_1 @ (k2_funct_1 @ X72) @ X73))
% 54.22/54.46          | ~ (v1_funct_1 @ X72)
% 54.22/54.46          | ~ (v1_relat_1 @ X72))),
% 54.22/54.46      inference('cnf', [status(esa)], [t154_funct_1])).
% 54.22/54.46  thf('197', plain,
% 54.22/54.46      (![X64 : $i]:
% 54.22/54.46         ((v1_relat_1 @ (k2_funct_1 @ X64))
% 54.22/54.46          | ~ (v1_funct_1 @ X64)
% 54.22/54.46          | ~ (v1_relat_1 @ X64))),
% 54.22/54.46      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 54.22/54.46  thf('198', plain,
% 54.22/54.46      (((k1_relat_1 @ (k2_funct_1 @ sk_B)) = (k2_relat_1 @ sk_B))),
% 54.22/54.46      inference('demod', [status(thm)], ['175', '176', '177', '178'])).
% 54.22/54.46  thf('199', plain,
% 54.22/54.46      (![X55 : $i, X56 : $i]:
% 54.22/54.46         ((r1_tarski @ (k10_relat_1 @ X55 @ X56) @ (k1_relat_1 @ X55))
% 54.22/54.46          | ~ (v1_relat_1 @ X55))),
% 54.22/54.46      inference('cnf', [status(esa)], [t167_relat_1])).
% 54.22/54.46  thf('200', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         ((r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ X0) @ 
% 54.22/54.46           (k2_relat_1 @ sk_B))
% 54.22/54.46          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 54.22/54.46      inference('sup+', [status(thm)], ['198', '199'])).
% 54.22/54.46  thf('201', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         (~ (v1_relat_1 @ sk_B)
% 54.22/54.46          | ~ (v1_funct_1 @ sk_B)
% 54.22/54.46          | (r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ X0) @ 
% 54.22/54.46             (k2_relat_1 @ sk_B)))),
% 54.22/54.46      inference('sup-', [status(thm)], ['197', '200'])).
% 54.22/54.46  thf('202', plain, ((v1_relat_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('203', plain, ((v1_funct_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('204', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         (r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ X0) @ 
% 54.22/54.46          (k2_relat_1 @ sk_B))),
% 54.22/54.46      inference('demod', [status(thm)], ['201', '202', '203'])).
% 54.22/54.46  thf('205', plain,
% 54.22/54.46      (![X70 : $i, X71 : $i]:
% 54.22/54.46         (~ (r1_tarski @ X70 @ (k2_relat_1 @ X71))
% 54.22/54.46          | ((k9_relat_1 @ X71 @ (k10_relat_1 @ X71 @ X70)) = (X70))
% 54.22/54.46          | ~ (v1_funct_1 @ X71)
% 54.22/54.46          | ~ (v1_relat_1 @ X71))),
% 54.22/54.46      inference('cnf', [status(esa)], [t147_funct_1])).
% 54.22/54.46  thf('206', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         (~ (v1_relat_1 @ sk_B)
% 54.22/54.46          | ~ (v1_funct_1 @ sk_B)
% 54.22/54.46          | ((k9_relat_1 @ sk_B @ 
% 54.22/54.46              (k10_relat_1 @ sk_B @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ X0)))
% 54.22/54.46              = (k10_relat_1 @ (k2_funct_1 @ sk_B) @ X0)))),
% 54.22/54.46      inference('sup-', [status(thm)], ['204', '205'])).
% 54.22/54.46  thf('207', plain, ((v1_relat_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('208', plain, ((v1_funct_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('209', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         ((k9_relat_1 @ sk_B @ 
% 54.22/54.46           (k10_relat_1 @ sk_B @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ X0)))
% 54.22/54.46           = (k10_relat_1 @ (k2_funct_1 @ sk_B) @ X0))),
% 54.22/54.46      inference('demod', [status(thm)], ['206', '207', '208'])).
% 54.22/54.46  thf('210', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ X0)))
% 54.22/54.46            = (k10_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 54.22/54.46          | ~ (v1_relat_1 @ sk_B)
% 54.22/54.46          | ~ (v1_funct_1 @ sk_B)
% 54.22/54.46          | ~ (v2_funct_1 @ sk_B))),
% 54.22/54.46      inference('sup+', [status(thm)], ['196', '209'])).
% 54.22/54.46  thf('211', plain,
% 54.22/54.46      (![X72 : $i, X73 : $i]:
% 54.22/54.46         (~ (v2_funct_1 @ X72)
% 54.22/54.46          | ((k9_relat_1 @ X72 @ X73)
% 54.22/54.46              = (k10_relat_1 @ (k2_funct_1 @ X72) @ X73))
% 54.22/54.46          | ~ (v1_funct_1 @ X72)
% 54.22/54.46          | ~ (v1_relat_1 @ X72))),
% 54.22/54.46      inference('cnf', [status(esa)], [t154_funct_1])).
% 54.22/54.46  thf('212', plain,
% 54.22/54.46      (![X64 : $i]:
% 54.22/54.46         ((v1_relat_1 @ (k2_funct_1 @ X64))
% 54.22/54.46          | ~ (v1_funct_1 @ X64)
% 54.22/54.46          | ~ (v1_relat_1 @ X64))),
% 54.22/54.46      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 54.22/54.46  thf('213', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         (~ (v1_relat_1 @ X0)
% 54.22/54.46          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 54.22/54.46             (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 54.22/54.46      inference('simplify', [status(thm)], ['11'])).
% 54.22/54.46  thf('214', plain,
% 54.22/54.46      (((k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)) = (k2_relat_1 @ sk_B))),
% 54.22/54.46      inference('demod', [status(thm)],
% 54.22/54.46                ['152', '153', '156', '157', '158', '159'])).
% 54.22/54.46  thf('215', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i]:
% 54.22/54.46         ((r1_tarski @ (k9_relat_1 @ X0 @ X1) @ 
% 54.22/54.46           (k1_relat_1 @ (k2_funct_1 @ X0)))
% 54.22/54.46          | ~ (v2_funct_1 @ X0)
% 54.22/54.46          | ~ (v1_funct_1 @ X0)
% 54.22/54.46          | ~ (v1_relat_1 @ X0))),
% 54.22/54.46      inference('simplify', [status(thm)], ['165'])).
% 54.22/54.46  thf('216', plain,
% 54.22/54.46      (((r1_tarski @ (k2_relat_1 @ sk_B) @ (k1_relat_1 @ (k2_funct_1 @ sk_B)))
% 54.22/54.46        | ~ (v1_relat_1 @ sk_B)
% 54.22/54.46        | ~ (v1_funct_1 @ sk_B)
% 54.22/54.46        | ~ (v2_funct_1 @ sk_B))),
% 54.22/54.46      inference('sup+', [status(thm)], ['214', '215'])).
% 54.22/54.46  thf('217', plain, ((v1_relat_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('218', plain, ((v1_funct_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('219', plain, ((v2_funct_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('220', plain,
% 54.22/54.46      ((r1_tarski @ (k2_relat_1 @ sk_B) @ (k1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 54.22/54.46      inference('demod', [status(thm)], ['216', '217', '218', '219'])).
% 54.22/54.46  thf('221', plain,
% 54.22/54.46      (![X14 : $i, X15 : $i, X16 : $i]:
% 54.22/54.46         (~ (r1_tarski @ X14 @ X15)
% 54.22/54.46          | ~ (r1_tarski @ X15 @ X16)
% 54.22/54.46          | (r1_tarski @ X14 @ X16))),
% 54.22/54.46      inference('cnf', [status(esa)], [t1_xboole_1])).
% 54.22/54.46  thf('222', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         ((r1_tarski @ (k2_relat_1 @ sk_B) @ X0)
% 54.22/54.46          | ~ (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_B)) @ X0))),
% 54.22/54.46      inference('sup-', [status(thm)], ['220', '221'])).
% 54.22/54.46  thf('223', plain,
% 54.22/54.46      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 54.22/54.46        | (r1_tarski @ (k2_relat_1 @ sk_B) @ 
% 54.22/54.46           (k10_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 54.22/54.46            (k2_relat_1 @ (k2_funct_1 @ sk_B)))))),
% 54.22/54.46      inference('sup-', [status(thm)], ['213', '222'])).
% 54.22/54.46  thf('224', plain,
% 54.22/54.46      ((~ (v1_relat_1 @ sk_B)
% 54.22/54.46        | ~ (v1_funct_1 @ sk_B)
% 54.22/54.46        | (r1_tarski @ (k2_relat_1 @ sk_B) @ 
% 54.22/54.46           (k10_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 54.22/54.46            (k2_relat_1 @ (k2_funct_1 @ sk_B)))))),
% 54.22/54.46      inference('sup-', [status(thm)], ['212', '223'])).
% 54.22/54.46  thf('225', plain, ((v1_relat_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('226', plain, ((v1_funct_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('227', plain,
% 54.22/54.46      ((r1_tarski @ (k2_relat_1 @ sk_B) @ 
% 54.22/54.46        (k10_relat_1 @ (k2_funct_1 @ sk_B) @ (k2_relat_1 @ (k2_funct_1 @ sk_B))))),
% 54.22/54.46      inference('demod', [status(thm)], ['224', '225', '226'])).
% 54.22/54.46  thf('228', plain,
% 54.22/54.46      (((r1_tarski @ (k2_relat_1 @ sk_B) @ 
% 54.22/54.46         (k9_relat_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_B))))
% 54.22/54.46        | ~ (v1_relat_1 @ sk_B)
% 54.22/54.46        | ~ (v1_funct_1 @ sk_B)
% 54.22/54.46        | ~ (v2_funct_1 @ sk_B))),
% 54.22/54.46      inference('sup+', [status(thm)], ['211', '227'])).
% 54.22/54.46  thf('229', plain, ((v1_relat_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('230', plain, ((v1_funct_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('231', plain, ((v2_funct_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('232', plain,
% 54.22/54.46      ((r1_tarski @ (k2_relat_1 @ sk_B) @ 
% 54.22/54.46        (k9_relat_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_B))))),
% 54.22/54.46      inference('demod', [status(thm)], ['228', '229', '230', '231'])).
% 54.22/54.46  thf('233', plain,
% 54.22/54.46      (![X47 : $i, X48 : $i]:
% 54.22/54.46         ((r1_tarski @ (k9_relat_1 @ X47 @ X48) @ (k2_relat_1 @ X47))
% 54.22/54.46          | ~ (v1_relat_1 @ X47))),
% 54.22/54.46      inference('cnf', [status(esa)], [t144_relat_1])).
% 54.22/54.46  thf('234', plain,
% 54.22/54.46      (![X14 : $i, X15 : $i, X16 : $i]:
% 54.22/54.46         (~ (r1_tarski @ X14 @ X15)
% 54.22/54.46          | ~ (r1_tarski @ X15 @ X16)
% 54.22/54.46          | (r1_tarski @ X14 @ X16))),
% 54.22/54.46      inference('cnf', [status(esa)], [t1_xboole_1])).
% 54.22/54.46  thf('235', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.22/54.46         (~ (v1_relat_1 @ X0)
% 54.22/54.46          | (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ X2)
% 54.22/54.46          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X2))),
% 54.22/54.46      inference('sup-', [status(thm)], ['233', '234'])).
% 54.22/54.46  thf('236', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         ((r1_tarski @ (k9_relat_1 @ sk_B @ X0) @ 
% 54.22/54.46           (k9_relat_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_B))))
% 54.22/54.46          | ~ (v1_relat_1 @ sk_B))),
% 54.22/54.46      inference('sup-', [status(thm)], ['232', '235'])).
% 54.22/54.46  thf('237', plain, ((v1_relat_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('238', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         (r1_tarski @ (k9_relat_1 @ sk_B @ X0) @ 
% 54.22/54.46          (k9_relat_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_B))))),
% 54.22/54.46      inference('demod', [status(thm)], ['236', '237'])).
% 54.22/54.46  thf('239', plain,
% 54.22/54.46      ((r1_tarski @ (k2_relat_1 @ sk_B) @ 
% 54.22/54.46        (k9_relat_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_B))))),
% 54.22/54.46      inference('demod', [status(thm)], ['228', '229', '230', '231'])).
% 54.22/54.46  thf('240', plain,
% 54.22/54.46      (![X0 : $i, X1 : $i]:
% 54.22/54.46         (~ (v1_relat_1 @ X0)
% 54.22/54.46          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ (k9_relat_1 @ X0 @ X1))
% 54.22/54.46          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ X1)))),
% 54.22/54.46      inference('sup-', [status(thm)], ['59', '60'])).
% 54.22/54.46  thf('241', plain,
% 54.22/54.46      ((((k2_relat_1 @ sk_B)
% 54.22/54.46          = (k9_relat_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_B))))
% 54.22/54.46        | ~ (v1_relat_1 @ sk_B))),
% 54.22/54.46      inference('sup-', [status(thm)], ['239', '240'])).
% 54.22/54.46  thf('242', plain, ((v1_relat_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('243', plain,
% 54.22/54.46      (((k2_relat_1 @ sk_B)
% 54.22/54.46         = (k9_relat_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_B))))),
% 54.22/54.46      inference('demod', [status(thm)], ['241', '242'])).
% 54.22/54.46  thf('244', plain,
% 54.22/54.46      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ sk_B @ X0) @ (k2_relat_1 @ sk_B))),
% 54.22/54.46      inference('demod', [status(thm)], ['238', '243'])).
% 54.22/54.46  thf('245', plain,
% 54.22/54.46      (![X70 : $i, X71 : $i]:
% 54.22/54.46         (~ (r1_tarski @ X70 @ (k2_relat_1 @ X71))
% 54.22/54.46          | ((k9_relat_1 @ X71 @ (k10_relat_1 @ X71 @ X70)) = (X70))
% 54.22/54.46          | ~ (v1_funct_1 @ X71)
% 54.22/54.46          | ~ (v1_relat_1 @ X71))),
% 54.22/54.46      inference('cnf', [status(esa)], [t147_funct_1])).
% 54.22/54.46  thf('246', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         (~ (v1_relat_1 @ sk_B)
% 54.22/54.46          | ~ (v1_funct_1 @ sk_B)
% 54.22/54.46          | ((k9_relat_1 @ sk_B @ 
% 54.22/54.46              (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ X0)))
% 54.22/54.46              = (k9_relat_1 @ sk_B @ X0)))),
% 54.22/54.46      inference('sup-', [status(thm)], ['244', '245'])).
% 54.22/54.46  thf('247', plain, ((v1_relat_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('248', plain, ((v1_funct_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('249', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         ((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ X0)))
% 54.22/54.46           = (k9_relat_1 @ sk_B @ X0))),
% 54.22/54.46      inference('demod', [status(thm)], ['246', '247', '248'])).
% 54.22/54.46  thf('250', plain, ((v1_relat_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('251', plain, ((v1_funct_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('252', plain, ((v2_funct_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('253', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         ((k9_relat_1 @ sk_B @ X0) = (k10_relat_1 @ (k2_funct_1 @ sk_B) @ X0))),
% 54.22/54.46      inference('demod', [status(thm)], ['210', '249', '250', '251', '252'])).
% 54.22/54.46  thf('254', plain,
% 54.22/54.46      (![X74 : $i, X75 : $i]:
% 54.22/54.46         (~ (v2_funct_1 @ X74)
% 54.22/54.46          | ((k10_relat_1 @ X74 @ X75)
% 54.22/54.46              = (k9_relat_1 @ (k2_funct_1 @ X74) @ X75))
% 54.22/54.46          | ~ (v1_funct_1 @ X74)
% 54.22/54.46          | ~ (v1_relat_1 @ X74))),
% 54.22/54.46      inference('cnf', [status(esa)], [t155_funct_1])).
% 54.22/54.46  thf('255', plain,
% 54.22/54.46      (![X64 : $i]:
% 54.22/54.46         ((v1_relat_1 @ (k2_funct_1 @ X64))
% 54.22/54.46          | ~ (v1_funct_1 @ X64)
% 54.22/54.46          | ~ (v1_relat_1 @ X64))),
% 54.22/54.46      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 54.22/54.46  thf('256', plain,
% 54.22/54.46      (((k1_relat_1 @ sk_B) = (k2_relat_1 @ (k2_funct_1 @ sk_B)))),
% 54.22/54.46      inference('demod', [status(thm)], ['191', '192'])).
% 54.22/54.46  thf('257', plain,
% 54.22/54.46      (![X47 : $i, X48 : $i]:
% 54.22/54.46         ((r1_tarski @ (k9_relat_1 @ X47 @ X48) @ (k2_relat_1 @ X47))
% 54.22/54.46          | ~ (v1_relat_1 @ X47))),
% 54.22/54.46      inference('cnf', [status(esa)], [t144_relat_1])).
% 54.22/54.46  thf('258', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         ((r1_tarski @ (k9_relat_1 @ (k2_funct_1 @ sk_B) @ X0) @ 
% 54.22/54.46           (k1_relat_1 @ sk_B))
% 54.22/54.46          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 54.22/54.46      inference('sup+', [status(thm)], ['256', '257'])).
% 54.22/54.46  thf('259', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         (~ (v1_relat_1 @ sk_B)
% 54.22/54.46          | ~ (v1_funct_1 @ sk_B)
% 54.22/54.46          | (r1_tarski @ (k9_relat_1 @ (k2_funct_1 @ sk_B) @ X0) @ 
% 54.22/54.46             (k1_relat_1 @ sk_B)))),
% 54.22/54.46      inference('sup-', [status(thm)], ['255', '258'])).
% 54.22/54.46  thf('260', plain, ((v1_relat_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('261', plain, ((v1_funct_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('262', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         (r1_tarski @ (k9_relat_1 @ (k2_funct_1 @ sk_B) @ X0) @ 
% 54.22/54.46          (k1_relat_1 @ sk_B))),
% 54.22/54.46      inference('demod', [status(thm)], ['259', '260', '261'])).
% 54.22/54.46  thf('263', plain,
% 54.22/54.46      (![X62 : $i, X63 : $i]:
% 54.22/54.46         (~ (r1_tarski @ X62 @ (k1_relat_1 @ X63))
% 54.22/54.46          | ((k1_relat_1 @ (k7_relat_1 @ X63 @ X62)) = (X62))
% 54.22/54.46          | ~ (v1_relat_1 @ X63))),
% 54.22/54.46      inference('cnf', [status(esa)], [t91_relat_1])).
% 54.22/54.46  thf('264', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         (~ (v1_relat_1 @ sk_B)
% 54.22/54.46          | ((k1_relat_1 @ 
% 54.22/54.46              (k7_relat_1 @ sk_B @ (k9_relat_1 @ (k2_funct_1 @ sk_B) @ X0)))
% 54.22/54.46              = (k9_relat_1 @ (k2_funct_1 @ sk_B) @ X0)))),
% 54.22/54.46      inference('sup-', [status(thm)], ['262', '263'])).
% 54.22/54.46  thf('265', plain, ((v1_relat_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('266', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         ((k1_relat_1 @ 
% 54.22/54.46           (k7_relat_1 @ sk_B @ (k9_relat_1 @ (k2_funct_1 @ sk_B) @ X0)))
% 54.22/54.46           = (k9_relat_1 @ (k2_funct_1 @ sk_B) @ X0))),
% 54.22/54.46      inference('demod', [status(thm)], ['264', '265'])).
% 54.22/54.46  thf('267', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         (((k1_relat_1 @ (k7_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ X0)))
% 54.22/54.46            = (k9_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 54.22/54.46          | ~ (v1_relat_1 @ sk_B)
% 54.22/54.46          | ~ (v1_funct_1 @ sk_B)
% 54.22/54.46          | ~ (v2_funct_1 @ sk_B))),
% 54.22/54.46      inference('sup+', [status(thm)], ['254', '266'])).
% 54.22/54.46  thf('268', plain,
% 54.22/54.46      (((k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))
% 54.22/54.46         = (k2_relat_1 @ (k2_funct_1 @ sk_B)))),
% 54.22/54.46      inference('demod', [status(thm)], ['186', '187', '188', '189'])).
% 54.22/54.46  thf('269', plain,
% 54.22/54.46      (((k1_relat_1 @ sk_B) = (k2_relat_1 @ (k2_funct_1 @ sk_B)))),
% 54.22/54.46      inference('demod', [status(thm)], ['191', '192'])).
% 54.22/54.46  thf('270', plain,
% 54.22/54.46      (((k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)) = (k1_relat_1 @ sk_B))),
% 54.22/54.46      inference('demod', [status(thm)], ['268', '269'])).
% 54.22/54.46  thf('271', plain,
% 54.22/54.46      (![X58 : $i, X59 : $i]:
% 54.22/54.46         ((r1_tarski @ (k10_relat_1 @ X58 @ X59) @ 
% 54.22/54.46           (k10_relat_1 @ X58 @ (k2_relat_1 @ X58)))
% 54.22/54.46          | ~ (v1_relat_1 @ X58))),
% 54.22/54.46      inference('cnf', [status(esa)], [t170_relat_1])).
% 54.22/54.46  thf('272', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         ((r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ (k1_relat_1 @ sk_B))
% 54.22/54.46          | ~ (v1_relat_1 @ sk_B))),
% 54.22/54.46      inference('sup+', [status(thm)], ['270', '271'])).
% 54.22/54.46  thf('273', plain, ((v1_relat_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('274', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         (r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ (k1_relat_1 @ sk_B))),
% 54.22/54.46      inference('demod', [status(thm)], ['272', '273'])).
% 54.22/54.46  thf('275', plain,
% 54.22/54.46      (![X62 : $i, X63 : $i]:
% 54.22/54.46         (~ (r1_tarski @ X62 @ (k1_relat_1 @ X63))
% 54.22/54.46          | ((k1_relat_1 @ (k7_relat_1 @ X63 @ X62)) = (X62))
% 54.22/54.46          | ~ (v1_relat_1 @ X63))),
% 54.22/54.46      inference('cnf', [status(esa)], [t91_relat_1])).
% 54.22/54.46  thf('276', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         (~ (v1_relat_1 @ sk_B)
% 54.22/54.46          | ((k1_relat_1 @ (k7_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ X0)))
% 54.22/54.46              = (k10_relat_1 @ sk_B @ X0)))),
% 54.22/54.46      inference('sup-', [status(thm)], ['274', '275'])).
% 54.22/54.46  thf('277', plain, ((v1_relat_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('278', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         ((k1_relat_1 @ (k7_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ X0)))
% 54.22/54.46           = (k10_relat_1 @ sk_B @ X0))),
% 54.22/54.46      inference('demod', [status(thm)], ['276', '277'])).
% 54.22/54.46  thf('279', plain, ((v1_relat_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('280', plain, ((v1_funct_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('281', plain, ((v2_funct_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('282', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         ((k10_relat_1 @ sk_B @ X0) = (k9_relat_1 @ (k2_funct_1 @ sk_B) @ X0))),
% 54.22/54.46      inference('demod', [status(thm)], ['267', '278', '279', '280', '281'])).
% 54.22/54.46  thf('283', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         (~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_B))
% 54.22/54.46          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 54.22/54.46          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 54.22/54.46          | ((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ X0)) = (X0)))),
% 54.22/54.46      inference('demod', [status(thm)], ['195', '253', '282'])).
% 54.22/54.46  thf('284', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         (~ (v1_relat_1 @ sk_B)
% 54.22/54.46          | ~ (v1_funct_1 @ sk_B)
% 54.22/54.46          | ((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ X0)) = (X0))
% 54.22/54.46          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 54.22/54.46          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_B)))),
% 54.22/54.46      inference('sup-', [status(thm)], ['2', '283'])).
% 54.22/54.46  thf('285', plain, ((v1_relat_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('286', plain, ((v1_funct_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('287', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         (((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ X0)) = (X0))
% 54.22/54.46          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 54.22/54.46          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_B)))),
% 54.22/54.46      inference('demod', [status(thm)], ['284', '285', '286'])).
% 54.22/54.46  thf('288', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         (~ (v1_relat_1 @ sk_B)
% 54.22/54.46          | ~ (v1_funct_1 @ sk_B)
% 54.22/54.46          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_B))
% 54.22/54.46          | ((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ X0)) = (X0)))),
% 54.22/54.46      inference('sup-', [status(thm)], ['1', '287'])).
% 54.22/54.46  thf('289', plain, ((v1_relat_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('290', plain, ((v1_funct_1 @ sk_B)),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('291', plain,
% 54.22/54.46      (![X0 : $i]:
% 54.22/54.46         (~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_B))
% 54.22/54.46          | ((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ X0)) = (X0)))),
% 54.22/54.46      inference('demod', [status(thm)], ['288', '289', '290'])).
% 54.22/54.46  thf('292', plain,
% 54.22/54.46      (((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 54.22/54.46      inference('sup-', [status(thm)], ['0', '291'])).
% 54.22/54.46  thf('293', plain,
% 54.22/54.46      (((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) != (sk_A))),
% 54.22/54.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.22/54.46  thf('294', plain, ($false),
% 54.22/54.46      inference('simplify_reflect-', [status(thm)], ['292', '293'])).
% 54.22/54.46  
% 54.22/54.46  % SZS output end Refutation
% 54.22/54.46  
% 54.22/54.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
