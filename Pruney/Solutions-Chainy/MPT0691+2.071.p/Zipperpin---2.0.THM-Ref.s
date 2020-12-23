%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yxcDXWtUhl

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:27 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 204 expanded)
%              Number of leaves         :   24 (  69 expanded)
%              Depth                    :   24
%              Number of atoms          :  722 (1720 expanded)
%              Number of equality atoms :   30 (  67 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

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

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) )
        = ( k9_relat_1 @ X15 @ X16 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X19: $i] :
      ( ( ( k10_relat_1 @ X19 @ ( k2_relat_1 @ X19 ) )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('7',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X19: $i] :
      ( ( ( k10_relat_1 @ X19 @ ( k2_relat_1 @ X19 ) )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X12 @ X11 )
      | ( r1_tarski @ ( k2_xboole_0 @ X10 @ X12 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ X0 ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X3 @ ( k2_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('23',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X17 @ X18 ) @ ( k1_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('24',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X3 @ ( k2_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k2_xboole_0 @ X2 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ X0 ) )
      | ( ( k1_relat_1 @ sk_B )
        = ( k10_relat_1 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ sk_B )
      = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','30'])).

thf('32',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('33',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('35',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X28 @ X27 ) @ X29 )
        = ( k3_xboole_0 @ X27 @ ( k10_relat_1 @ X28 @ X29 ) ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('36',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X17 @ X18 ) @ ( k1_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['34','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['9','42'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('44',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X23 @ X24 ) ) @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('45',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_A
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X17 @ X18 ) @ ( k1_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) )
      | ( sk_A
        = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( sk_A
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','56'])).

thf('58',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('59',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('60',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( sk_A
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('62',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X25 @ X26 ) @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t179_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('63',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( r1_tarski @ ( k10_relat_1 @ X21 @ X22 ) @ ( k10_relat_1 @ X20 @ X22 ) )
      | ~ ( r1_tarski @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t179_relat_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k10_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k10_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k10_relat_1 @ X0 @ X2 ) ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['61','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    $false ),
    inference(demod,[status(thm)],['0','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yxcDXWtUhl
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:58:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.69/0.90  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.69/0.90  % Solved by: fo/fo7.sh
% 0.69/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.90  % done 943 iterations in 0.476s
% 0.69/0.90  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.69/0.90  % SZS output start Refutation
% 0.69/0.90  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.69/0.90  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.69/0.90  thf(sk_B_type, type, sk_B: $i).
% 0.69/0.90  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.69/0.90  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.69/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.90  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.69/0.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.69/0.90  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.69/0.90  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.69/0.90  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.69/0.90  thf(t146_funct_1, conjecture,
% 0.69/0.90    (![A:$i,B:$i]:
% 0.69/0.90     ( ( v1_relat_1 @ B ) =>
% 0.69/0.90       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.69/0.90         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.69/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.90    (~( ![A:$i,B:$i]:
% 0.69/0.90        ( ( v1_relat_1 @ B ) =>
% 0.69/0.90          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.69/0.90            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 0.69/0.90    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 0.69/0.90  thf('0', plain,
% 0.69/0.90      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf(t148_relat_1, axiom,
% 0.69/0.90    (![A:$i,B:$i]:
% 0.69/0.90     ( ( v1_relat_1 @ B ) =>
% 0.69/0.90       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.69/0.90  thf('1', plain,
% 0.69/0.90      (![X15 : $i, X16 : $i]:
% 0.69/0.90         (((k2_relat_1 @ (k7_relat_1 @ X15 @ X16)) = (k9_relat_1 @ X15 @ X16))
% 0.69/0.90          | ~ (v1_relat_1 @ X15))),
% 0.69/0.90      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.69/0.90  thf(t169_relat_1, axiom,
% 0.69/0.90    (![A:$i]:
% 0.69/0.90     ( ( v1_relat_1 @ A ) =>
% 0.69/0.90       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.69/0.90  thf('2', plain,
% 0.69/0.90      (![X19 : $i]:
% 0.69/0.90         (((k10_relat_1 @ X19 @ (k2_relat_1 @ X19)) = (k1_relat_1 @ X19))
% 0.69/0.90          | ~ (v1_relat_1 @ X19))),
% 0.69/0.90      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.69/0.90  thf('3', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i]:
% 0.69/0.90         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.69/0.90            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.69/0.90          | ~ (v1_relat_1 @ X1)
% 0.69/0.90          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.69/0.90      inference('sup+', [status(thm)], ['1', '2'])).
% 0.69/0.90  thf(dt_k7_relat_1, axiom,
% 0.69/0.90    (![A:$i,B:$i]:
% 0.69/0.90     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.69/0.90  thf('4', plain,
% 0.69/0.90      (![X13 : $i, X14 : $i]:
% 0.69/0.90         (~ (v1_relat_1 @ X13) | (v1_relat_1 @ (k7_relat_1 @ X13 @ X14)))),
% 0.69/0.90      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.69/0.90  thf('5', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i]:
% 0.69/0.90         (~ (v1_relat_1 @ X1)
% 0.69/0.90          | ((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.69/0.90              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.69/0.90      inference('clc', [status(thm)], ['3', '4'])).
% 0.69/0.90  thf('6', plain,
% 0.69/0.90      (![X13 : $i, X14 : $i]:
% 0.69/0.90         (~ (v1_relat_1 @ X13) | (v1_relat_1 @ (k7_relat_1 @ X13 @ X14)))),
% 0.69/0.90      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.69/0.90  thf('7', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf(t28_xboole_1, axiom,
% 0.69/0.90    (![A:$i,B:$i]:
% 0.69/0.90     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.69/0.90  thf('8', plain,
% 0.69/0.90      (![X6 : $i, X7 : $i]:
% 0.69/0.90         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.69/0.90      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.69/0.90  thf('9', plain, (((k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (sk_A))),
% 0.69/0.90      inference('sup-', [status(thm)], ['7', '8'])).
% 0.69/0.90  thf('10', plain,
% 0.69/0.90      (![X19 : $i]:
% 0.69/0.90         (((k10_relat_1 @ X19 @ (k2_relat_1 @ X19)) = (k1_relat_1 @ X19))
% 0.69/0.90          | ~ (v1_relat_1 @ X19))),
% 0.69/0.90      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.69/0.90  thf(d10_xboole_0, axiom,
% 0.69/0.90    (![A:$i,B:$i]:
% 0.69/0.90     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.69/0.90  thf('11', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.69/0.90      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.69/0.90  thf('12', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.69/0.90      inference('simplify', [status(thm)], ['11'])).
% 0.69/0.90  thf('13', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf(t8_xboole_1, axiom,
% 0.69/0.90    (![A:$i,B:$i,C:$i]:
% 0.69/0.90     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.69/0.90       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.69/0.90  thf('14', plain,
% 0.69/0.90      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.69/0.90         (~ (r1_tarski @ X10 @ X11)
% 0.69/0.90          | ~ (r1_tarski @ X12 @ X11)
% 0.69/0.90          | (r1_tarski @ (k2_xboole_0 @ X10 @ X12) @ X11))),
% 0.69/0.90      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.69/0.90  thf('15', plain,
% 0.69/0.90      (![X0 : $i]:
% 0.69/0.90         ((r1_tarski @ (k2_xboole_0 @ sk_A @ X0) @ (k1_relat_1 @ sk_B))
% 0.69/0.90          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_B)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['13', '14'])).
% 0.69/0.90  thf('16', plain,
% 0.69/0.90      ((r1_tarski @ (k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) @ 
% 0.69/0.90        (k1_relat_1 @ sk_B))),
% 0.69/0.90      inference('sup-', [status(thm)], ['12', '15'])).
% 0.69/0.90  thf('17', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.69/0.90      inference('simplify', [status(thm)], ['11'])).
% 0.69/0.90  thf(t10_xboole_1, axiom,
% 0.69/0.90    (![A:$i,B:$i,C:$i]:
% 0.69/0.90     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.69/0.90  thf('18', plain,
% 0.69/0.90      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.69/0.90         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ X3 @ (k2_xboole_0 @ X5 @ X4)))),
% 0.69/0.90      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.69/0.90  thf('19', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.69/0.90      inference('sup-', [status(thm)], ['17', '18'])).
% 0.69/0.90  thf('20', plain,
% 0.69/0.90      (![X0 : $i, X2 : $i]:
% 0.69/0.90         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.69/0.90      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.69/0.90  thf('21', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i]:
% 0.69/0.90         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.69/0.90          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['19', '20'])).
% 0.69/0.90  thf('22', plain,
% 0.69/0.90      (((k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (k1_relat_1 @ sk_B))),
% 0.69/0.90      inference('sup-', [status(thm)], ['16', '21'])).
% 0.69/0.90  thf(t167_relat_1, axiom,
% 0.69/0.90    (![A:$i,B:$i]:
% 0.69/0.90     ( ( v1_relat_1 @ B ) =>
% 0.69/0.90       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.69/0.90  thf('23', plain,
% 0.69/0.90      (![X17 : $i, X18 : $i]:
% 0.69/0.90         ((r1_tarski @ (k10_relat_1 @ X17 @ X18) @ (k1_relat_1 @ X17))
% 0.69/0.90          | ~ (v1_relat_1 @ X17))),
% 0.69/0.90      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.69/0.90  thf('24', plain,
% 0.69/0.90      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.69/0.90         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ X3 @ (k2_xboole_0 @ X5 @ X4)))),
% 0.69/0.90      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.69/0.90  thf('25', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.90         (~ (v1_relat_1 @ X0)
% 0.69/0.90          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ 
% 0.69/0.90             (k2_xboole_0 @ X2 @ (k1_relat_1 @ X0))))),
% 0.69/0.90      inference('sup-', [status(thm)], ['23', '24'])).
% 0.69/0.90  thf('26', plain,
% 0.69/0.90      (![X0 : $i]:
% 0.69/0.90         ((r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ (k1_relat_1 @ sk_B))
% 0.69/0.90          | ~ (v1_relat_1 @ sk_B))),
% 0.69/0.90      inference('sup+', [status(thm)], ['22', '25'])).
% 0.69/0.90  thf('27', plain, ((v1_relat_1 @ sk_B)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('28', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         (r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ (k1_relat_1 @ sk_B))),
% 0.69/0.91      inference('demod', [status(thm)], ['26', '27'])).
% 0.69/0.91  thf('29', plain,
% 0.69/0.91      (![X0 : $i, X2 : $i]:
% 0.69/0.91         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.69/0.91      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.69/0.91  thf('30', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         (~ (r1_tarski @ (k1_relat_1 @ sk_B) @ (k10_relat_1 @ sk_B @ X0))
% 0.69/0.91          | ((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ X0)))),
% 0.69/0.91      inference('sup-', [status(thm)], ['28', '29'])).
% 0.69/0.91  thf('31', plain,
% 0.69/0.91      ((~ (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B))
% 0.69/0.91        | ~ (v1_relat_1 @ sk_B)
% 0.69/0.91        | ((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))))),
% 0.69/0.91      inference('sup-', [status(thm)], ['10', '30'])).
% 0.69/0.91  thf('32', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.69/0.91      inference('simplify', [status(thm)], ['11'])).
% 0.69/0.91  thf('33', plain, ((v1_relat_1 @ sk_B)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('34', plain,
% 0.69/0.91      (((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 0.69/0.91      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.69/0.91  thf(t139_funct_1, axiom,
% 0.69/0.91    (![A:$i,B:$i,C:$i]:
% 0.69/0.91     ( ( v1_relat_1 @ C ) =>
% 0.69/0.91       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.69/0.91         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.69/0.91  thf('35', plain,
% 0.69/0.91      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.69/0.91         (((k10_relat_1 @ (k7_relat_1 @ X28 @ X27) @ X29)
% 0.69/0.91            = (k3_xboole_0 @ X27 @ (k10_relat_1 @ X28 @ X29)))
% 0.69/0.91          | ~ (v1_relat_1 @ X28))),
% 0.69/0.91      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.69/0.91  thf('36', plain,
% 0.69/0.91      (![X17 : $i, X18 : $i]:
% 0.69/0.91         ((r1_tarski @ (k10_relat_1 @ X17 @ X18) @ (k1_relat_1 @ X17))
% 0.69/0.91          | ~ (v1_relat_1 @ X17))),
% 0.69/0.91      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.69/0.91  thf('37', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.91         ((r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 0.69/0.91           (k1_relat_1 @ (k7_relat_1 @ X1 @ X2)))
% 0.69/0.91          | ~ (v1_relat_1 @ X1)
% 0.69/0.91          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2)))),
% 0.69/0.91      inference('sup+', [status(thm)], ['35', '36'])).
% 0.69/0.91  thf('38', plain,
% 0.69/0.91      (![X13 : $i, X14 : $i]:
% 0.69/0.91         (~ (v1_relat_1 @ X13) | (v1_relat_1 @ (k7_relat_1 @ X13 @ X14)))),
% 0.69/0.91      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.69/0.91  thf('39', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.91         (~ (v1_relat_1 @ X1)
% 0.69/0.91          | (r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 0.69/0.91             (k1_relat_1 @ (k7_relat_1 @ X1 @ X2))))),
% 0.69/0.91      inference('clc', [status(thm)], ['37', '38'])).
% 0.69/0.91  thf('40', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         ((r1_tarski @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ sk_B)) @ 
% 0.69/0.91           (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))
% 0.69/0.91          | ~ (v1_relat_1 @ sk_B))),
% 0.69/0.91      inference('sup+', [status(thm)], ['34', '39'])).
% 0.69/0.91  thf('41', plain, ((v1_relat_1 @ sk_B)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('42', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         (r1_tarski @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ sk_B)) @ 
% 0.69/0.91          (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))),
% 0.69/0.91      inference('demod', [status(thm)], ['40', '41'])).
% 0.69/0.91  thf('43', plain,
% 0.69/0.91      ((r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.69/0.91      inference('sup+', [status(thm)], ['9', '42'])).
% 0.69/0.91  thf(t87_relat_1, axiom,
% 0.69/0.91    (![A:$i,B:$i]:
% 0.69/0.91     ( ( v1_relat_1 @ B ) =>
% 0.69/0.91       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.69/0.91  thf('44', plain,
% 0.69/0.91      (![X23 : $i, X24 : $i]:
% 0.69/0.91         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X23 @ X24)) @ X24)
% 0.69/0.91          | ~ (v1_relat_1 @ X23))),
% 0.69/0.91      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.69/0.91  thf('45', plain,
% 0.69/0.91      (![X0 : $i, X2 : $i]:
% 0.69/0.91         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.69/0.91      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.69/0.91  thf('46', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i]:
% 0.69/0.91         (~ (v1_relat_1 @ X1)
% 0.69/0.91          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.69/0.91          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.69/0.91      inference('sup-', [status(thm)], ['44', '45'])).
% 0.69/0.91  thf('47', plain,
% 0.69/0.91      ((((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.69/0.91        | ~ (v1_relat_1 @ sk_B))),
% 0.69/0.91      inference('sup-', [status(thm)], ['43', '46'])).
% 0.69/0.91  thf('48', plain, ((v1_relat_1 @ sk_B)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('49', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.69/0.91      inference('demod', [status(thm)], ['47', '48'])).
% 0.69/0.91  thf('50', plain,
% 0.69/0.91      (![X17 : $i, X18 : $i]:
% 0.69/0.91         ((r1_tarski @ (k10_relat_1 @ X17 @ X18) @ (k1_relat_1 @ X17))
% 0.69/0.91          | ~ (v1_relat_1 @ X17))),
% 0.69/0.91      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.69/0.91  thf('51', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ sk_A)
% 0.69/0.91          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.69/0.91      inference('sup+', [status(thm)], ['49', '50'])).
% 0.69/0.91  thf('52', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         (~ (v1_relat_1 @ sk_B)
% 0.69/0.91          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ sk_A))),
% 0.69/0.91      inference('sup-', [status(thm)], ['6', '51'])).
% 0.69/0.91  thf('53', plain, ((v1_relat_1 @ sk_B)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('54', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ sk_A)),
% 0.69/0.91      inference('demod', [status(thm)], ['52', '53'])).
% 0.69/0.91  thf('55', plain,
% 0.69/0.91      (![X0 : $i, X2 : $i]:
% 0.69/0.91         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.69/0.91      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.69/0.91  thf('56', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         (~ (r1_tarski @ sk_A @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0))
% 0.69/0.91          | ((sk_A) = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0)))),
% 0.69/0.91      inference('sup-', [status(thm)], ['54', '55'])).
% 0.69/0.91  thf('57', plain,
% 0.69/0.91      ((~ (r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.69/0.91        | ~ (v1_relat_1 @ sk_B)
% 0.69/0.91        | ((sk_A)
% 0.69/0.91            = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.69/0.91               (k9_relat_1 @ sk_B @ sk_A))))),
% 0.69/0.91      inference('sup-', [status(thm)], ['5', '56'])).
% 0.69/0.91  thf('58', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.69/0.91      inference('demod', [status(thm)], ['47', '48'])).
% 0.69/0.91  thf('59', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.69/0.91      inference('simplify', [status(thm)], ['11'])).
% 0.69/0.91  thf('60', plain, ((v1_relat_1 @ sk_B)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('61', plain,
% 0.69/0.91      (((sk_A)
% 0.69/0.91         = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.69/0.91            (k9_relat_1 @ sk_B @ sk_A)))),
% 0.69/0.91      inference('demod', [status(thm)], ['57', '58', '59', '60'])).
% 0.69/0.91  thf(t88_relat_1, axiom,
% 0.69/0.91    (![A:$i,B:$i]:
% 0.69/0.91     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.69/0.91  thf('62', plain,
% 0.69/0.91      (![X25 : $i, X26 : $i]:
% 0.69/0.91         ((r1_tarski @ (k7_relat_1 @ X25 @ X26) @ X25) | ~ (v1_relat_1 @ X25))),
% 0.69/0.91      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.69/0.91  thf(t179_relat_1, axiom,
% 0.69/0.91    (![A:$i,B:$i]:
% 0.69/0.91     ( ( v1_relat_1 @ B ) =>
% 0.69/0.91       ( ![C:$i]:
% 0.69/0.91         ( ( v1_relat_1 @ C ) =>
% 0.69/0.91           ( ( r1_tarski @ B @ C ) =>
% 0.69/0.91             ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.69/0.91  thf('63', plain,
% 0.69/0.91      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.69/0.91         (~ (v1_relat_1 @ X20)
% 0.69/0.91          | (r1_tarski @ (k10_relat_1 @ X21 @ X22) @ (k10_relat_1 @ X20 @ X22))
% 0.69/0.91          | ~ (r1_tarski @ X21 @ X20)
% 0.69/0.91          | ~ (v1_relat_1 @ X21))),
% 0.69/0.91      inference('cnf', [status(esa)], [t179_relat_1])).
% 0.69/0.91  thf('64', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.91         (~ (v1_relat_1 @ X0)
% 0.69/0.91          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.69/0.91          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X2) @ 
% 0.69/0.91             (k10_relat_1 @ X0 @ X2))
% 0.69/0.91          | ~ (v1_relat_1 @ X0))),
% 0.69/0.91      inference('sup-', [status(thm)], ['62', '63'])).
% 0.69/0.91  thf('65', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.91         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X2) @ 
% 0.69/0.91           (k10_relat_1 @ X0 @ X2))
% 0.69/0.91          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.69/0.91          | ~ (v1_relat_1 @ X0))),
% 0.69/0.91      inference('simplify', [status(thm)], ['64'])).
% 0.69/0.91  thf('66', plain,
% 0.69/0.91      (![X13 : $i, X14 : $i]:
% 0.69/0.91         (~ (v1_relat_1 @ X13) | (v1_relat_1 @ (k7_relat_1 @ X13 @ X14)))),
% 0.69/0.91      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.69/0.91  thf('67', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.91         (~ (v1_relat_1 @ X0)
% 0.69/0.91          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X2) @ 
% 0.69/0.91             (k10_relat_1 @ X0 @ X2)))),
% 0.69/0.91      inference('clc', [status(thm)], ['65', '66'])).
% 0.69/0.91  thf('68', plain,
% 0.69/0.91      (((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.69/0.91        | ~ (v1_relat_1 @ sk_B))),
% 0.69/0.91      inference('sup+', [status(thm)], ['61', '67'])).
% 0.69/0.91  thf('69', plain, ((v1_relat_1 @ sk_B)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('70', plain,
% 0.69/0.91      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.69/0.91      inference('demod', [status(thm)], ['68', '69'])).
% 0.69/0.91  thf('71', plain, ($false), inference('demod', [status(thm)], ['0', '70'])).
% 0.69/0.91  
% 0.69/0.91  % SZS output end Refutation
% 0.69/0.91  
% 0.69/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
