%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Bme5255meb

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:25 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 152 expanded)
%              Number of leaves         :   30 (  58 expanded)
%              Depth                    :   26
%              Number of atoms          :  631 (1217 expanded)
%              Number of equality atoms :   55 (  87 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

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
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X42 @ X41 ) @ X43 )
        = ( k3_xboole_0 @ X41 @ ( k10_relat_1 @ X42 @ X43 ) ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t162_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
            = ( k9_relat_1 @ A @ B ) ) ) ) )).

thf('5',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ X27 @ X28 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X29 @ X28 ) @ X27 )
        = ( k9_relat_1 @ X29 @ X27 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t162_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X0 )
        = ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('8',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k7_relat_1 @ X40 @ X39 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X39 ) @ X40 ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('9',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X32 @ X31 ) )
        = ( k10_relat_1 @ X32 @ ( k1_relat_1 @ X31 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('10',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('11',plain,(
    ! [X34: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X34 ) )
      = X34 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('12',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X35 ) @ X36 )
      | ( ( k5_relat_1 @ X35 @ ( k6_relat_1 @ X36 ) )
        = X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('14',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X33: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('18',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X32 @ X31 ) )
        = ( k10_relat_1 @ X32 @ ( k1_relat_1 @ X31 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) )
      = ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X33: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('24',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('25',plain,
    ( sk_A
    = ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ( sk_A
      = ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','25'])).

thf('27',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('28',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ( sk_A
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('33',plain,(
    ! [X26: $i] :
      ( ( ( k9_relat_1 @ X26 @ ( k1_relat_1 @ X26 ) )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('34',plain,
    ( ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
    = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['6','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('41',plain,(
    ! [X30: $i] :
      ( ( ( k10_relat_1 @ X30 @ ( k2_relat_1 @ X30 ) )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('42',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('44',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['2','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['48','49'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('51',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('52',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('53',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('54',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['52','53'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('55',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('56',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['0','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Bme5255meb
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:20:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.41/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.59  % Solved by: fo/fo7.sh
% 0.41/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.59  % done 232 iterations in 0.136s
% 0.41/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.59  % SZS output start Refutation
% 0.41/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.41/0.59  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.41/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.59  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.41/0.59  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.41/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.41/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.59  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.41/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.41/0.59  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.41/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.41/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.59  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.41/0.59  thf(t146_funct_1, conjecture,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( v1_relat_1 @ B ) =>
% 0.41/0.59       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.41/0.59         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.41/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.59    (~( ![A:$i,B:$i]:
% 0.41/0.59        ( ( v1_relat_1 @ B ) =>
% 0.41/0.59          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.41/0.59            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 0.41/0.59    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 0.41/0.59  thf('0', plain,
% 0.41/0.59      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(t139_funct_1, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( v1_relat_1 @ C ) =>
% 0.41/0.59       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.41/0.59         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.41/0.59  thf('1', plain,
% 0.41/0.59      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.41/0.59         (((k10_relat_1 @ (k7_relat_1 @ X42 @ X41) @ X43)
% 0.41/0.59            = (k3_xboole_0 @ X41 @ (k10_relat_1 @ X42 @ X43)))
% 0.41/0.59          | ~ (v1_relat_1 @ X42))),
% 0.41/0.59      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.41/0.59  thf(dt_k7_relat_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.41/0.59  thf('2', plain,
% 0.41/0.59      (![X24 : $i, X25 : $i]:
% 0.41/0.59         (~ (v1_relat_1 @ X24) | (v1_relat_1 @ (k7_relat_1 @ X24 @ X25)))),
% 0.41/0.59      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.41/0.59  thf(d10_xboole_0, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.41/0.59  thf('3', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.41/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.59  thf('4', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.41/0.59      inference('simplify', [status(thm)], ['3'])).
% 0.41/0.59  thf(t162_relat_1, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( v1_relat_1 @ A ) =>
% 0.41/0.59       ( ![B:$i,C:$i]:
% 0.41/0.59         ( ( r1_tarski @ B @ C ) =>
% 0.41/0.59           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 0.41/0.59             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 0.41/0.59  thf('5', plain,
% 0.41/0.59      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.41/0.59         (~ (r1_tarski @ X27 @ X28)
% 0.41/0.59          | ((k9_relat_1 @ (k7_relat_1 @ X29 @ X28) @ X27)
% 0.41/0.59              = (k9_relat_1 @ X29 @ X27))
% 0.41/0.59          | ~ (v1_relat_1 @ X29))),
% 0.41/0.59      inference('cnf', [status(esa)], [t162_relat_1])).
% 0.41/0.59  thf('6', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (~ (v1_relat_1 @ X1)
% 0.41/0.59          | ((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X0)
% 0.41/0.59              = (k9_relat_1 @ X1 @ X0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['4', '5'])).
% 0.41/0.59  thf('7', plain,
% 0.41/0.59      (![X24 : $i, X25 : $i]:
% 0.41/0.59         (~ (v1_relat_1 @ X24) | (v1_relat_1 @ (k7_relat_1 @ X24 @ X25)))),
% 0.41/0.59      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.41/0.59  thf(t94_relat_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( v1_relat_1 @ B ) =>
% 0.41/0.59       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.41/0.59  thf('8', plain,
% 0.41/0.59      (![X39 : $i, X40 : $i]:
% 0.41/0.59         (((k7_relat_1 @ X40 @ X39) = (k5_relat_1 @ (k6_relat_1 @ X39) @ X40))
% 0.41/0.59          | ~ (v1_relat_1 @ X40))),
% 0.41/0.59      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.41/0.59  thf(t182_relat_1, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( v1_relat_1 @ A ) =>
% 0.41/0.59       ( ![B:$i]:
% 0.41/0.59         ( ( v1_relat_1 @ B ) =>
% 0.41/0.59           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.41/0.59             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.41/0.59  thf('9', plain,
% 0.41/0.59      (![X31 : $i, X32 : $i]:
% 0.41/0.59         (~ (v1_relat_1 @ X31)
% 0.41/0.59          | ((k1_relat_1 @ (k5_relat_1 @ X32 @ X31))
% 0.41/0.59              = (k10_relat_1 @ X32 @ (k1_relat_1 @ X31)))
% 0.41/0.59          | ~ (v1_relat_1 @ X32))),
% 0.41/0.59      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.41/0.59  thf('10', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(t71_relat_1, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.41/0.59       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.41/0.59  thf('11', plain, (![X34 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X34)) = (X34))),
% 0.41/0.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.41/0.59  thf(t79_relat_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( v1_relat_1 @ B ) =>
% 0.41/0.59       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.41/0.59         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.41/0.59  thf('12', plain,
% 0.41/0.59      (![X35 : $i, X36 : $i]:
% 0.41/0.59         (~ (r1_tarski @ (k2_relat_1 @ X35) @ X36)
% 0.41/0.59          | ((k5_relat_1 @ X35 @ (k6_relat_1 @ X36)) = (X35))
% 0.41/0.59          | ~ (v1_relat_1 @ X35))),
% 0.41/0.59      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.41/0.59  thf('13', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (~ (r1_tarski @ X0 @ X1)
% 0.41/0.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.41/0.59          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.41/0.59              = (k6_relat_1 @ X0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['11', '12'])).
% 0.41/0.59  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.41/0.59  thf('14', plain, (![X23 : $i]: (v1_relat_1 @ (k6_relat_1 @ X23))),
% 0.41/0.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.41/0.59  thf('15', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (~ (r1_tarski @ X0 @ X1)
% 0.41/0.59          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.41/0.59              = (k6_relat_1 @ X0)))),
% 0.41/0.59      inference('demod', [status(thm)], ['13', '14'])).
% 0.41/0.59  thf('16', plain,
% 0.41/0.59      (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 0.41/0.59         = (k6_relat_1 @ sk_A))),
% 0.41/0.59      inference('sup-', [status(thm)], ['10', '15'])).
% 0.41/0.59  thf('17', plain, (![X33 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X33)) = (X33))),
% 0.41/0.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.41/0.59  thf('18', plain,
% 0.41/0.59      (![X31 : $i, X32 : $i]:
% 0.41/0.59         (~ (v1_relat_1 @ X31)
% 0.41/0.59          | ((k1_relat_1 @ (k5_relat_1 @ X32 @ X31))
% 0.41/0.59              = (k10_relat_1 @ X32 @ (k1_relat_1 @ X31)))
% 0.41/0.59          | ~ (v1_relat_1 @ X32))),
% 0.41/0.59      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.41/0.59  thf('19', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.41/0.59            = (k10_relat_1 @ X1 @ X0))
% 0.41/0.59          | ~ (v1_relat_1 @ X1)
% 0.41/0.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.41/0.59      inference('sup+', [status(thm)], ['17', '18'])).
% 0.41/0.59  thf('20', plain, (![X23 : $i]: (v1_relat_1 @ (k6_relat_1 @ X23))),
% 0.41/0.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.41/0.59  thf('21', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.41/0.59            = (k10_relat_1 @ X1 @ X0))
% 0.41/0.59          | ~ (v1_relat_1 @ X1))),
% 0.41/0.59      inference('demod', [status(thm)], ['19', '20'])).
% 0.41/0.59  thf('22', plain,
% 0.41/0.59      ((((k1_relat_1 @ (k6_relat_1 @ sk_A))
% 0.41/0.59          = (k10_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)))
% 0.41/0.59        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.41/0.59      inference('sup+', [status(thm)], ['16', '21'])).
% 0.41/0.59  thf('23', plain, (![X33 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X33)) = (X33))),
% 0.41/0.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.41/0.59  thf('24', plain, (![X23 : $i]: (v1_relat_1 @ (k6_relat_1 @ X23))),
% 0.41/0.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.41/0.59  thf('25', plain,
% 0.41/0.59      (((sk_A) = (k10_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 0.41/0.59      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.41/0.59  thf('26', plain,
% 0.41/0.59      ((((sk_A) = (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)))
% 0.41/0.59        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 0.41/0.59        | ~ (v1_relat_1 @ sk_B))),
% 0.41/0.59      inference('sup+', [status(thm)], ['9', '25'])).
% 0.41/0.59  thf('27', plain, (![X23 : $i]: (v1_relat_1 @ (k6_relat_1 @ X23))),
% 0.41/0.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.41/0.59  thf('28', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('29', plain,
% 0.41/0.59      (((sk_A) = (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)))),
% 0.41/0.59      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.41/0.59  thf('30', plain,
% 0.41/0.59      ((((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.41/0.59        | ~ (v1_relat_1 @ sk_B))),
% 0.41/0.59      inference('sup+', [status(thm)], ['8', '29'])).
% 0.41/0.59  thf('31', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('32', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.41/0.59      inference('demod', [status(thm)], ['30', '31'])).
% 0.41/0.59  thf(t146_relat_1, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( v1_relat_1 @ A ) =>
% 0.41/0.59       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.41/0.59  thf('33', plain,
% 0.41/0.59      (![X26 : $i]:
% 0.41/0.59         (((k9_relat_1 @ X26 @ (k1_relat_1 @ X26)) = (k2_relat_1 @ X26))
% 0.41/0.59          | ~ (v1_relat_1 @ X26))),
% 0.41/0.59      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.41/0.59  thf('34', plain,
% 0.41/0.59      ((((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.41/0.59          = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.41/0.59        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.41/0.59      inference('sup+', [status(thm)], ['32', '33'])).
% 0.41/0.59  thf('35', plain,
% 0.41/0.59      ((~ (v1_relat_1 @ sk_B)
% 0.41/0.59        | ((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.41/0.59            = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.41/0.59      inference('sup-', [status(thm)], ['7', '34'])).
% 0.41/0.59  thf('36', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('37', plain,
% 0.41/0.59      (((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.41/0.59         = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.41/0.59      inference('demod', [status(thm)], ['35', '36'])).
% 0.41/0.59  thf('38', plain,
% 0.41/0.59      ((((k9_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.41/0.59        | ~ (v1_relat_1 @ sk_B))),
% 0.41/0.59      inference('sup+', [status(thm)], ['6', '37'])).
% 0.41/0.59  thf('39', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('40', plain,
% 0.41/0.59      (((k9_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.41/0.59      inference('demod', [status(thm)], ['38', '39'])).
% 0.41/0.59  thf(t169_relat_1, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( v1_relat_1 @ A ) =>
% 0.41/0.59       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.41/0.59  thf('41', plain,
% 0.41/0.59      (![X30 : $i]:
% 0.41/0.59         (((k10_relat_1 @ X30 @ (k2_relat_1 @ X30)) = (k1_relat_1 @ X30))
% 0.41/0.59          | ~ (v1_relat_1 @ X30))),
% 0.41/0.59      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.41/0.59  thf('42', plain,
% 0.41/0.59      ((((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A))
% 0.41/0.59          = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.41/0.59        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.41/0.59      inference('sup+', [status(thm)], ['40', '41'])).
% 0.41/0.59  thf('43', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.41/0.59      inference('demod', [status(thm)], ['30', '31'])).
% 0.41/0.59  thf('44', plain,
% 0.41/0.59      ((((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A))
% 0.41/0.59          = (sk_A))
% 0.41/0.59        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.41/0.59      inference('demod', [status(thm)], ['42', '43'])).
% 0.41/0.59  thf('45', plain,
% 0.41/0.59      ((~ (v1_relat_1 @ sk_B)
% 0.41/0.59        | ((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.41/0.59            (k9_relat_1 @ sk_B @ sk_A)) = (sk_A)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['2', '44'])).
% 0.41/0.59  thf('46', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('47', plain,
% 0.41/0.59      (((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A))
% 0.41/0.59         = (sk_A))),
% 0.41/0.59      inference('demod', [status(thm)], ['45', '46'])).
% 0.41/0.59  thf('48', plain,
% 0.41/0.59      ((((k3_xboole_0 @ sk_A @ 
% 0.41/0.59          (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))) = (sk_A))
% 0.41/0.59        | ~ (v1_relat_1 @ sk_B))),
% 0.41/0.59      inference('sup+', [status(thm)], ['1', '47'])).
% 0.41/0.59  thf('49', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('50', plain,
% 0.41/0.59      (((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.41/0.59         = (sk_A))),
% 0.41/0.59      inference('demod', [status(thm)], ['48', '49'])).
% 0.41/0.59  thf(t100_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.41/0.59  thf('51', plain,
% 0.41/0.59      (![X6 : $i, X7 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ X6 @ X7)
% 0.41/0.59           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.41/0.59  thf('52', plain,
% 0.41/0.59      (((k4_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.41/0.59         = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.41/0.59      inference('sup+', [status(thm)], ['50', '51'])).
% 0.41/0.59  thf(t92_xboole_1, axiom,
% 0.41/0.59    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.41/0.59  thf('53', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ X11) = (k1_xboole_0))),
% 0.41/0.59      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.41/0.59  thf('54', plain,
% 0.41/0.59      (((k4_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.41/0.59         = (k1_xboole_0))),
% 0.41/0.59      inference('demod', [status(thm)], ['52', '53'])).
% 0.41/0.59  thf(l32_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.41/0.59  thf('55', plain,
% 0.41/0.59      (![X3 : $i, X4 : $i]:
% 0.41/0.59         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.41/0.59      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.41/0.59  thf('56', plain,
% 0.41/0.59      ((((k1_xboole_0) != (k1_xboole_0))
% 0.41/0.59        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 0.41/0.59      inference('sup-', [status(thm)], ['54', '55'])).
% 0.41/0.59  thf('57', plain,
% 0.41/0.59      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.41/0.59      inference('simplify', [status(thm)], ['56'])).
% 0.41/0.59  thf('58', plain, ($false), inference('demod', [status(thm)], ['0', '57'])).
% 0.41/0.59  
% 0.41/0.59  % SZS output end Refutation
% 0.41/0.59  
% 0.41/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
