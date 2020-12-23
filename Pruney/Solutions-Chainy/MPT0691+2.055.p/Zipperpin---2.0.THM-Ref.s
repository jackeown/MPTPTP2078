%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xLb7pDCHDw

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:25 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 272 expanded)
%              Number of leaves         :   29 (  96 expanded)
%              Depth                    :   24
%              Number of atoms          :  803 (2370 expanded)
%              Number of equality atoms :   64 ( 148 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t146_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
         => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t146_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X41 @ X40 ) @ X42 )
        = ( k3_xboole_0 @ X40 @ ( k10_relat_1 @ X41 @ X42 ) ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X27 @ X28 ) )
        = ( k9_relat_1 @ X27 @ X28 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('4',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('5',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('6',plain,(
    ! [X32: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X32 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('7',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X36 ) @ X37 )
      | ( ( k7_relat_1 @ X36 @ X37 )
        = X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf(t189_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ B ) )
            = ( k7_relat_1 @ A @ ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v1_relat_1 @ X30 )
      | ( ( k7_relat_1 @ X31 @ ( k1_relat_1 @ X30 ) )
        = ( k7_relat_1 @ X31 @ ( k1_relat_1 @ ( k7_relat_1 @ X30 @ ( k1_relat_1 @ X31 ) ) ) ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t189_relat_1])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('13',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X34 @ X35 ) ) @ X35 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X32: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X32 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('18',plain,(
    ! [X32: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X32 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('19',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('20',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf('22',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X34 @ X35 ) ) @ X35 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( sk_A
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X36 ) @ X37 )
      | ( ( k7_relat_1 @ X36 @ X37 )
        = X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k7_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k7_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['27','31'])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k7_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k7_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
    = ( k7_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X27 @ X28 ) )
        = ( k9_relat_1 @ X27 @ X28 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('37',plain,(
    ! [X29: $i] :
      ( ( ( k10_relat_1 @ X29 @ ( k2_relat_1 @ X29 ) )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('43',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('45',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X27 @ X28 ) )
        = ( k9_relat_1 @ X27 @ X28 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['43','47'])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k7_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
    = ( k7_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('53',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('54',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
      = sk_A )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','51','52','53'])).

thf('55',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['3','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['61','62'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('64',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('65',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('67',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['28'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('70',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['68','71'])).

thf('73',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['65','72'])).

thf('74',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( ( k4_xboole_0 @ X4 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('75',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    $false ),
    inference(demod,[status(thm)],['0','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xLb7pDCHDw
% 0.14/0.33  % Computer   : n003.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:13:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 120 iterations in 0.052s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.50  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.50  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(t146_funct_1, conjecture,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ B ) =>
% 0.20/0.50       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.50         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i]:
% 0.20/0.50        ( ( v1_relat_1 @ B ) =>
% 0.20/0.50          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.50            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t139_funct_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ C ) =>
% 0.20/0.50       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.20/0.50         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.20/0.50         (((k10_relat_1 @ (k7_relat_1 @ X41 @ X40) @ X42)
% 0.20/0.50            = (k3_xboole_0 @ X40 @ (k10_relat_1 @ X41 @ X42)))
% 0.20/0.50          | ~ (v1_relat_1 @ X41))),
% 0.20/0.50      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.20/0.50  thf(t148_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ B ) =>
% 0.20/0.50       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X27 : $i, X28 : $i]:
% 0.20/0.50         (((k2_relat_1 @ (k7_relat_1 @ X27 @ X28)) = (k9_relat_1 @ X27 @ X28))
% 0.20/0.50          | ~ (v1_relat_1 @ X27))),
% 0.20/0.50      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.50  thf(dt_k7_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X25 : $i, X26 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X25) | (v1_relat_1 @ (k7_relat_1 @ X25 @ X26)))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X25 : $i, X26 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X25) | (v1_relat_1 @ (k7_relat_1 @ X25 @ X26)))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.20/0.50  thf('5', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t71_relat_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.20/0.50       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.50  thf('6', plain, (![X32 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X32)) = (X32))),
% 0.20/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.50  thf(t97_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ B ) =>
% 0.20/0.50       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.20/0.50         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X36 : $i, X37 : $i]:
% 0.20/0.50         (~ (r1_tarski @ (k1_relat_1 @ X36) @ X37)
% 0.20/0.50          | ((k7_relat_1 @ X36 @ X37) = (X36))
% 0.20/0.50          | ~ (v1_relat_1 @ X36))),
% 0.20/0.50      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.50          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf(fc3_funct_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.20/0.50       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.20/0.50  thf('9', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.50          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.20/0.50         = (k6_relat_1 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['5', '10'])).
% 0.20/0.50  thf(t189_relat_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( v1_relat_1 @ B ) =>
% 0.20/0.50           ( ( k7_relat_1 @ A @ ( k1_relat_1 @ B ) ) =
% 0.20/0.50             ( k7_relat_1 @
% 0.20/0.50               A @ ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X30 : $i, X31 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X30)
% 0.20/0.50          | ((k7_relat_1 @ X31 @ (k1_relat_1 @ X30))
% 0.20/0.50              = (k7_relat_1 @ X31 @ 
% 0.20/0.50                 (k1_relat_1 @ (k7_relat_1 @ X30 @ (k1_relat_1 @ X31)))))
% 0.20/0.50          | ~ (v1_relat_1 @ X31))),
% 0.20/0.50      inference('cnf', [status(esa)], [t189_relat_1])).
% 0.20/0.50  thf(t87_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ B ) =>
% 0.20/0.50       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X34 : $i, X35 : $i]:
% 0.20/0.50         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X34 @ X35)) @ X35)
% 0.20/0.50          | ~ (v1_relat_1 @ X34))),
% 0.20/0.50      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0))) @ 
% 0.20/0.50           (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1))))
% 0.20/0.50          | ~ (v1_relat_1 @ X1)
% 0.20/0.50          | ~ (v1_relat_1 @ X0)
% 0.20/0.50          | ~ (v1_relat_1 @ X1))),
% 0.20/0.50      inference('sup+', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X0)
% 0.20/0.50          | ~ (v1_relat_1 @ X1)
% 0.20/0.50          | (r1_tarski @ 
% 0.20/0.50             (k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0))) @ 
% 0.20/0.50             (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1)))))),
% 0.20/0.50      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (((r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ sk_A)) @ 
% 0.20/0.50         (k1_relat_1 @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ (k6_relat_1 @ sk_A)))))
% 0.20/0.50        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 0.20/0.50        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.50      inference('sup+', [status(thm)], ['11', '15'])).
% 0.20/0.50  thf('17', plain, (![X32 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X32)) = (X32))),
% 0.20/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.50  thf('18', plain, (![X32 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X32)) = (X32))),
% 0.20/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.50  thf('19', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.50  thf('20', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      ((r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X34 : $i, X35 : $i]:
% 0.20/0.50         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X34 @ X35)) @ X35)
% 0.20/0.50          | ~ (v1_relat_1 @ X34))),
% 0.20/0.50      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.20/0.50  thf(d10_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X1 : $i, X3 : $i]:
% 0.20/0.50         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X1)
% 0.20/0.50          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.20/0.50          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      ((((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.20/0.50        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['21', '24'])).
% 0.20/0.50  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('27', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.50  thf('29', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.20/0.50      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      (![X36 : $i, X37 : $i]:
% 0.20/0.50         (~ (r1_tarski @ (k1_relat_1 @ X36) @ X37)
% 0.20/0.50          | ((k7_relat_1 @ X36 @ X37) = (X36))
% 0.20/0.50          | ~ (v1_relat_1 @ X36))),
% 0.20/0.50      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      ((((k7_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.20/0.50          = (k7_relat_1 @ sk_B @ sk_A))
% 0.20/0.50        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['27', '31'])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.50        | ((k7_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.20/0.50            = (k7_relat_1 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['4', '32'])).
% 0.20/0.50  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      (((k7_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.20/0.50         = (k7_relat_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (![X27 : $i, X28 : $i]:
% 0.20/0.50         (((k2_relat_1 @ (k7_relat_1 @ X27 @ X28)) = (k9_relat_1 @ X27 @ X28))
% 0.20/0.50          | ~ (v1_relat_1 @ X27))),
% 0.20/0.50      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.50  thf(t169_relat_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) =>
% 0.20/0.50       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      (![X29 : $i]:
% 0.20/0.50         (((k10_relat_1 @ X29 @ (k2_relat_1 @ X29)) = (k1_relat_1 @ X29))
% 0.20/0.50          | ~ (v1_relat_1 @ X29))),
% 0.20/0.50      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.20/0.50            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.20/0.50          | ~ (v1_relat_1 @ X1)
% 0.20/0.50          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['36', '37'])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      (![X25 : $i, X26 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X25) | (v1_relat_1 @ (k7_relat_1 @ X25 @ X26)))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.20/0.50  thf('40', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X1)
% 0.20/0.50          | ((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.20/0.50              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.20/0.50      inference('clc', [status(thm)], ['38', '39'])).
% 0.20/0.50  thf('41', plain,
% 0.20/0.50      ((((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.20/0.50          (k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A))
% 0.20/0.50          = (k1_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)))
% 0.20/0.50        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['35', '40'])).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      (![X25 : $i, X26 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X25) | (v1_relat_1 @ (k7_relat_1 @ X25 @ X26)))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.20/0.50  thf('43', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      (![X27 : $i, X28 : $i]:
% 0.20/0.50         (((k2_relat_1 @ (k7_relat_1 @ X27 @ X28)) = (k9_relat_1 @ X27 @ X28))
% 0.20/0.50          | ~ (v1_relat_1 @ X27))),
% 0.20/0.50      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.50  thf('46', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.20/0.50          | ~ (v1_relat_1 @ X0)
% 0.20/0.50          | ~ (v1_relat_1 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['44', '45'])).
% 0.20/0.50  thf('47', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X0)
% 0.20/0.50          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.20/0.50      inference('simplify', [status(thm)], ['46'])).
% 0.20/0.50  thf('48', plain,
% 0.20/0.50      ((((k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.20/0.50          = (k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A))
% 0.20/0.50        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['43', '47'])).
% 0.20/0.50  thf('49', plain,
% 0.20/0.50      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.50        | ((k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.20/0.50            = (k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['42', '48'])).
% 0.20/0.50  thf('50', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('51', plain,
% 0.20/0.50      (((k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.20/0.50         = (k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.50  thf('52', plain,
% 0.20/0.50      (((k7_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.20/0.50         = (k7_relat_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.50  thf('53', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.50  thf('54', plain,
% 0.20/0.50      ((((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.20/0.50          (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))) = (sk_A))
% 0.20/0.50        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['41', '51', '52', '53'])).
% 0.20/0.50  thf('55', plain,
% 0.20/0.50      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.50        | ((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.20/0.50            (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))) = (sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['3', '54'])).
% 0.20/0.50  thf('56', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('57', plain,
% 0.20/0.50      (((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.20/0.50         (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))) = (sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['55', '56'])).
% 0.20/0.50  thf('58', plain,
% 0.20/0.50      ((((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A))
% 0.20/0.50          = (sk_A))
% 0.20/0.50        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.50      inference('sup+', [status(thm)], ['2', '57'])).
% 0.20/0.50  thf('59', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('60', plain,
% 0.20/0.50      (((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A))
% 0.20/0.50         = (sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['58', '59'])).
% 0.20/0.50  thf('61', plain,
% 0.20/0.50      ((((k3_xboole_0 @ sk_A @ 
% 0.20/0.50          (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))) = (sk_A))
% 0.20/0.50        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.50      inference('sup+', [status(thm)], ['1', '60'])).
% 0.20/0.50  thf('62', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('63', plain,
% 0.20/0.50      (((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.20/0.50         = (sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['61', '62'])).
% 0.20/0.50  thf(t100_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.50  thf('64', plain,
% 0.20/0.50      (![X7 : $i, X8 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ X7 @ X8)
% 0.20/0.50           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.50  thf('65', plain,
% 0.20/0.50      (((k4_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.20/0.50         = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.20/0.50      inference('sup+', [status(thm)], ['63', '64'])).
% 0.20/0.50  thf(idempotence_k3_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.50  thf('66', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.20/0.50  thf('67', plain,
% 0.20/0.50      (![X7 : $i, X8 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ X7 @ X8)
% 0.20/0.50           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.50  thf('68', plain,
% 0.20/0.50      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['66', '67'])).
% 0.20/0.50  thf('69', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.20/0.50      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.50  thf(l32_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.50  thf('70', plain,
% 0.20/0.50      (![X4 : $i, X6 : $i]:
% 0.20/0.50         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.20/0.50      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.50  thf('71', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['69', '70'])).
% 0.20/0.50  thf('72', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['68', '71'])).
% 0.20/0.50  thf('73', plain,
% 0.20/0.50      (((k4_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.20/0.50         = (k1_xboole_0))),
% 0.20/0.50      inference('demod', [status(thm)], ['65', '72'])).
% 0.20/0.50  thf('74', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i]:
% 0.20/0.50         ((r1_tarski @ X4 @ X5) | ((k4_xboole_0 @ X4 @ X5) != (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.50  thf('75', plain,
% 0.20/0.50      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.50        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['73', '74'])).
% 0.20/0.50  thf('76', plain,
% 0.20/0.50      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['75'])).
% 0.20/0.50  thf('77', plain, ($false), inference('demod', [status(thm)], ['0', '76'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
