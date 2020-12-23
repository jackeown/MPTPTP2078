%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Lkc1PKpM4c

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:55 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 263 expanded)
%              Number of leaves         :   30 (  91 expanded)
%              Depth                    :   16
%              Number of atoms          :  674 (2026 expanded)
%              Number of equality atoms :   62 ( 172 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t25_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
          = ( k2_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k3_subset_1 @ X34 @ X35 )
        = ( k4_xboole_0 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k4_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('4',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = sk_A ),
    inference('sup+',[status(thm)],['2','3'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('6',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ sk_A ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ sk_A ) @ sk_A )
    = ( k3_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['6','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('15',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ sk_A ) )
    = ( k3_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ sk_A ) )
    = ( k5_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = ( k3_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = ( k3_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ sk_A ) )
    = ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k5_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ sk_A ) )
    = ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['17','24'])).

thf('26',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k4_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ sk_A ) ) @ sk_A ),
    inference('sup+',[status(thm)],['25','28'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('30',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ X23 @ X24 )
      | ( r2_hidden @ X23 @ X25 )
      | ( X25
       != ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('31',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r2_hidden @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    r2_hidden @ ( k5_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('33',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X30 @ X31 )
      | ( m1_subset_1 @ X30 @ X31 )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('35',plain,(
    ! [X30: $i,X31: $i] :
      ( ( m1_subset_1 @ X30 @ X31 )
      | ~ ( r2_hidden @ X30 @ X31 ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ X31 )
      | ( r2_hidden @ X30 @ X31 )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('40',plain,(
    ! [X36: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('41',plain,(
    r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X26 @ X25 )
      | ( r1_tarski @ X26 @ X24 )
      | ( X25
       != ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('43',plain,(
    ! [X24: $i,X26: $i] :
      ( ( r1_tarski @ X26 @ X24 )
      | ~ ( r2_hidden @ X26 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('46',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['36','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('49',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) )
      | ( ( k4_subset_1 @ X38 @ X37 @ X39 )
        = ( k2_xboole_0 @ X37 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B_1 @ X0 )
        = ( k2_xboole_0 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B_1 @ ( k5_xboole_0 @ sk_A @ sk_B_1 ) )
    = ( k2_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ sk_A ) )
    = ( k5_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('53',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['44','45'])).

thf('54',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['44','45'])).

thf('55',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = ( k5_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k4_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('57',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) @ ( k5_xboole_0 @ sk_A @ sk_B_1 ) )
    = sk_A ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('59',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['44','45'])).

thf('60',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ sk_A @ sk_B_1 ) )
    = sk_A ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B_1 @ ( k5_xboole_0 @ sk_A @ sk_B_1 ) )
    = sk_A ),
    inference(demod,[status(thm)],['51','60'])).

thf('62',plain,(
    ( k4_subset_1 @ sk_A @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('63',plain,(
    ! [X33: $i] :
      ( ( k2_subset_1 @ X33 )
      = X33 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('64',plain,(
    ( k4_subset_1 @ sk_A @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
 != sk_A ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = ( k5_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('66',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('67',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k5_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ( k4_subset_1 @ sk_A @ sk_B_1 @ ( k5_xboole_0 @ sk_A @ sk_B_1 ) )
 != sk_A ),
    inference(demod,[status(thm)],['64','67'])).

thf('69',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['61','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Lkc1PKpM4c
% 0.14/0.38  % Computer   : n015.cluster.edu
% 0.14/0.38  % Model      : x86_64 x86_64
% 0.14/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.38  % Memory     : 8042.1875MB
% 0.14/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.38  % CPULimit   : 60
% 0.14/0.38  % DateTime   : Tue Dec  1 19:28:08 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.39  % Python version: Python 3.6.8
% 0.14/0.39  % Running in FO mode
% 0.25/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.59  % Solved by: fo/fo7.sh
% 0.25/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.59  % done 252 iterations in 0.094s
% 0.25/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.59  % SZS output start Refutation
% 0.25/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.25/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.25/0.59  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.25/0.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.25/0.59  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.25/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.25/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.25/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.25/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.25/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.25/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.25/0.59  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.25/0.59  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.25/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.25/0.59  thf(t25_subset_1, conjecture,
% 0.25/0.59    (![A:$i,B:$i]:
% 0.25/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.25/0.59       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.25/0.59         ( k2_subset_1 @ A ) ) ))).
% 0.25/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.59    (~( ![A:$i,B:$i]:
% 0.25/0.59        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.25/0.59          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.25/0.59            ( k2_subset_1 @ A ) ) ) )),
% 0.25/0.59    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 0.25/0.59  thf('0', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.25/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.59  thf(d5_subset_1, axiom,
% 0.25/0.59    (![A:$i,B:$i]:
% 0.25/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.25/0.59       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.25/0.59  thf('1', plain,
% 0.25/0.59      (![X34 : $i, X35 : $i]:
% 0.25/0.59         (((k3_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))
% 0.25/0.59          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 0.25/0.59      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.25/0.59  thf('2', plain,
% 0.25/0.59      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.25/0.59      inference('sup-', [status(thm)], ['0', '1'])).
% 0.25/0.59  thf(t51_xboole_1, axiom,
% 0.25/0.59    (![A:$i,B:$i]:
% 0.25/0.59     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.25/0.59       ( A ) ))).
% 0.25/0.59  thf('3', plain,
% 0.25/0.59      (![X16 : $i, X17 : $i]:
% 0.25/0.59         ((k2_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ (k4_xboole_0 @ X16 @ X17))
% 0.25/0.59           = (X16))),
% 0.25/0.59      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.25/0.59  thf('4', plain,
% 0.25/0.59      (((k2_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B_1) @ 
% 0.25/0.59         (k3_subset_1 @ sk_A @ sk_B_1)) = (sk_A))),
% 0.25/0.59      inference('sup+', [status(thm)], ['2', '3'])).
% 0.25/0.59  thf(commutativity_k3_xboole_0, axiom,
% 0.25/0.59    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.25/0.59  thf('5', plain,
% 0.25/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.25/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.25/0.59  thf('6', plain,
% 0.25/0.59      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ sk_A) @ 
% 0.25/0.59         (k3_subset_1 @ sk_A @ sk_B_1)) = (sk_A))),
% 0.25/0.59      inference('demod', [status(thm)], ['4', '5'])).
% 0.25/0.59  thf(t46_xboole_1, axiom,
% 0.25/0.59    (![A:$i,B:$i]:
% 0.25/0.59     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.25/0.59  thf('7', plain,
% 0.25/0.59      (![X12 : $i, X13 : $i]:
% 0.25/0.59         ((k4_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13)) = (k1_xboole_0))),
% 0.25/0.59      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.25/0.59  thf(l32_xboole_1, axiom,
% 0.25/0.59    (![A:$i,B:$i]:
% 0.25/0.59     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.25/0.59  thf('8', plain,
% 0.25/0.59      (![X5 : $i, X6 : $i]:
% 0.25/0.59         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 0.25/0.59      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.25/0.59  thf('9', plain,
% 0.25/0.59      (![X0 : $i, X1 : $i]:
% 0.25/0.59         (((k1_xboole_0) != (k1_xboole_0))
% 0.25/0.59          | (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.25/0.59      inference('sup-', [status(thm)], ['7', '8'])).
% 0.25/0.59  thf('10', plain,
% 0.25/0.59      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.25/0.59      inference('simplify', [status(thm)], ['9'])).
% 0.25/0.59  thf(t28_xboole_1, axiom,
% 0.25/0.59    (![A:$i,B:$i]:
% 0.25/0.59     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.25/0.59  thf('11', plain,
% 0.25/0.59      (![X10 : $i, X11 : $i]:
% 0.25/0.59         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.25/0.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.25/0.59  thf('12', plain,
% 0.25/0.59      (![X0 : $i, X1 : $i]:
% 0.25/0.59         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.25/0.59      inference('sup-', [status(thm)], ['10', '11'])).
% 0.25/0.59  thf('13', plain,
% 0.25/0.59      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ sk_A) @ sk_A)
% 0.25/0.59         = (k3_xboole_0 @ sk_B_1 @ sk_A))),
% 0.25/0.59      inference('sup+', [status(thm)], ['6', '12'])).
% 0.25/0.59  thf('14', plain,
% 0.25/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.25/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.25/0.59  thf('15', plain,
% 0.25/0.59      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ sk_A))
% 0.25/0.59         = (k3_xboole_0 @ sk_B_1 @ sk_A))),
% 0.25/0.59      inference('demod', [status(thm)], ['13', '14'])).
% 0.25/0.59  thf(t100_xboole_1, axiom,
% 0.25/0.59    (![A:$i,B:$i]:
% 0.25/0.59     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.25/0.59  thf('16', plain,
% 0.25/0.59      (![X8 : $i, X9 : $i]:
% 0.25/0.59         ((k4_xboole_0 @ X8 @ X9)
% 0.25/0.59           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.25/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.25/0.59  thf('17', plain,
% 0.25/0.59      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ sk_A))
% 0.25/0.59         = (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.25/0.59      inference('sup+', [status(thm)], ['15', '16'])).
% 0.25/0.59  thf('18', plain,
% 0.25/0.59      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.25/0.59      inference('sup-', [status(thm)], ['0', '1'])).
% 0.25/0.59  thf(t48_xboole_1, axiom,
% 0.25/0.59    (![A:$i,B:$i]:
% 0.25/0.59     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.25/0.59  thf('19', plain,
% 0.25/0.59      (![X14 : $i, X15 : $i]:
% 0.25/0.59         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.25/0.59           = (k3_xboole_0 @ X14 @ X15))),
% 0.25/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.25/0.59  thf('20', plain,
% 0.25/0.59      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.25/0.59         = (k3_xboole_0 @ sk_A @ sk_B_1))),
% 0.25/0.59      inference('sup+', [status(thm)], ['18', '19'])).
% 0.25/0.59  thf('21', plain,
% 0.25/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.25/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.25/0.59  thf('22', plain,
% 0.25/0.59      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.25/0.59         = (k3_xboole_0 @ sk_B_1 @ sk_A))),
% 0.25/0.59      inference('demod', [status(thm)], ['20', '21'])).
% 0.25/0.59  thf('23', plain,
% 0.25/0.59      (![X14 : $i, X15 : $i]:
% 0.25/0.59         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.25/0.59           = (k3_xboole_0 @ X14 @ X15))),
% 0.25/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.25/0.59  thf('24', plain,
% 0.25/0.59      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ sk_A))
% 0.25/0.59         = (k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.25/0.59      inference('sup+', [status(thm)], ['22', '23'])).
% 0.25/0.59  thf('25', plain,
% 0.25/0.59      (((k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ sk_A))
% 0.25/0.59         = (k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.25/0.59      inference('sup+', [status(thm)], ['17', '24'])).
% 0.25/0.59  thf('26', plain,
% 0.25/0.59      (![X16 : $i, X17 : $i]:
% 0.25/0.59         ((k2_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ (k4_xboole_0 @ X16 @ X17))
% 0.25/0.59           = (X16))),
% 0.25/0.59      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.25/0.59  thf('27', plain,
% 0.25/0.59      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.25/0.59      inference('simplify', [status(thm)], ['9'])).
% 0.25/0.59  thf('28', plain,
% 0.25/0.59      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.25/0.59      inference('sup+', [status(thm)], ['26', '27'])).
% 0.25/0.59  thf('29', plain,
% 0.25/0.59      ((r1_tarski @ (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ sk_A)) @ sk_A)),
% 0.25/0.59      inference('sup+', [status(thm)], ['25', '28'])).
% 0.25/0.59  thf(d1_zfmisc_1, axiom,
% 0.25/0.59    (![A:$i,B:$i]:
% 0.25/0.59     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.25/0.59       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.25/0.59  thf('30', plain,
% 0.25/0.59      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.25/0.59         (~ (r1_tarski @ X23 @ X24)
% 0.25/0.59          | (r2_hidden @ X23 @ X25)
% 0.25/0.59          | ((X25) != (k1_zfmisc_1 @ X24)))),
% 0.25/0.59      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.25/0.59  thf('31', plain,
% 0.25/0.59      (![X23 : $i, X24 : $i]:
% 0.25/0.59         ((r2_hidden @ X23 @ (k1_zfmisc_1 @ X24)) | ~ (r1_tarski @ X23 @ X24))),
% 0.25/0.59      inference('simplify', [status(thm)], ['30'])).
% 0.25/0.59  thf('32', plain,
% 0.25/0.59      ((r2_hidden @ (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ sk_A)) @ 
% 0.25/0.59        (k1_zfmisc_1 @ sk_A))),
% 0.25/0.59      inference('sup-', [status(thm)], ['29', '31'])).
% 0.25/0.59  thf(d2_subset_1, axiom,
% 0.25/0.59    (![A:$i,B:$i]:
% 0.25/0.59     ( ( ( v1_xboole_0 @ A ) =>
% 0.25/0.59         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.25/0.59       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.25/0.59         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.25/0.59  thf('33', plain,
% 0.25/0.59      (![X30 : $i, X31 : $i]:
% 0.25/0.59         (~ (r2_hidden @ X30 @ X31)
% 0.25/0.59          | (m1_subset_1 @ X30 @ X31)
% 0.25/0.59          | (v1_xboole_0 @ X31))),
% 0.25/0.59      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.25/0.59  thf(d1_xboole_0, axiom,
% 0.25/0.59    (![A:$i]:
% 0.25/0.59     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.25/0.59  thf('34', plain,
% 0.25/0.59      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.25/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.25/0.59  thf('35', plain,
% 0.25/0.59      (![X30 : $i, X31 : $i]:
% 0.25/0.59         ((m1_subset_1 @ X30 @ X31) | ~ (r2_hidden @ X30 @ X31))),
% 0.25/0.59      inference('clc', [status(thm)], ['33', '34'])).
% 0.25/0.59  thf('36', plain,
% 0.25/0.59      ((m1_subset_1 @ (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ sk_A)) @ 
% 0.25/0.59        (k1_zfmisc_1 @ sk_A))),
% 0.25/0.59      inference('sup-', [status(thm)], ['32', '35'])).
% 0.25/0.59  thf('37', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.25/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.59  thf('38', plain,
% 0.25/0.59      (![X30 : $i, X31 : $i]:
% 0.25/0.59         (~ (m1_subset_1 @ X30 @ X31)
% 0.25/0.59          | (r2_hidden @ X30 @ X31)
% 0.25/0.59          | (v1_xboole_0 @ X31))),
% 0.25/0.59      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.25/0.59  thf('39', plain,
% 0.25/0.59      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.25/0.59        | (r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.25/0.59      inference('sup-', [status(thm)], ['37', '38'])).
% 0.25/0.59  thf(fc1_subset_1, axiom,
% 0.25/0.59    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.25/0.59  thf('40', plain, (![X36 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X36))),
% 0.25/0.59      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.25/0.59  thf('41', plain, ((r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.25/0.59      inference('clc', [status(thm)], ['39', '40'])).
% 0.25/0.59  thf('42', plain,
% 0.25/0.59      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.25/0.59         (~ (r2_hidden @ X26 @ X25)
% 0.25/0.59          | (r1_tarski @ X26 @ X24)
% 0.25/0.59          | ((X25) != (k1_zfmisc_1 @ X24)))),
% 0.25/0.59      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.25/0.59  thf('43', plain,
% 0.25/0.59      (![X24 : $i, X26 : $i]:
% 0.25/0.59         ((r1_tarski @ X26 @ X24) | ~ (r2_hidden @ X26 @ (k1_zfmisc_1 @ X24)))),
% 0.25/0.59      inference('simplify', [status(thm)], ['42'])).
% 0.25/0.59  thf('44', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 0.25/0.59      inference('sup-', [status(thm)], ['41', '43'])).
% 0.25/0.59  thf('45', plain,
% 0.25/0.59      (![X10 : $i, X11 : $i]:
% 0.25/0.59         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.25/0.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.25/0.59  thf('46', plain, (((k3_xboole_0 @ sk_B_1 @ sk_A) = (sk_B_1))),
% 0.25/0.59      inference('sup-', [status(thm)], ['44', '45'])).
% 0.25/0.59  thf('47', plain,
% 0.25/0.59      ((m1_subset_1 @ (k5_xboole_0 @ sk_A @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.25/0.59      inference('demod', [status(thm)], ['36', '46'])).
% 0.25/0.59  thf('48', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.25/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.59  thf(redefinition_k4_subset_1, axiom,
% 0.25/0.59    (![A:$i,B:$i,C:$i]:
% 0.25/0.59     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.25/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.25/0.59       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.25/0.59  thf('49', plain,
% 0.25/0.59      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.25/0.59         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38))
% 0.25/0.59          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38))
% 0.25/0.59          | ((k4_subset_1 @ X38 @ X37 @ X39) = (k2_xboole_0 @ X37 @ X39)))),
% 0.25/0.59      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.25/0.59  thf('50', plain,
% 0.25/0.59      (![X0 : $i]:
% 0.25/0.59         (((k4_subset_1 @ sk_A @ sk_B_1 @ X0) = (k2_xboole_0 @ sk_B_1 @ X0))
% 0.25/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.25/0.59      inference('sup-', [status(thm)], ['48', '49'])).
% 0.25/0.59  thf('51', plain,
% 0.25/0.59      (((k4_subset_1 @ sk_A @ sk_B_1 @ (k5_xboole_0 @ sk_A @ sk_B_1))
% 0.25/0.59         = (k2_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ sk_A @ sk_B_1)))),
% 0.25/0.59      inference('sup-', [status(thm)], ['47', '50'])).
% 0.25/0.59  thf('52', plain,
% 0.25/0.59      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ sk_A))
% 0.25/0.59         = (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.25/0.59      inference('sup+', [status(thm)], ['15', '16'])).
% 0.25/0.59  thf('53', plain, (((k3_xboole_0 @ sk_B_1 @ sk_A) = (sk_B_1))),
% 0.25/0.59      inference('sup-', [status(thm)], ['44', '45'])).
% 0.25/0.59  thf('54', plain, (((k3_xboole_0 @ sk_B_1 @ sk_A) = (sk_B_1))),
% 0.25/0.59      inference('sup-', [status(thm)], ['44', '45'])).
% 0.25/0.59  thf('55', plain,
% 0.25/0.59      (((k4_xboole_0 @ sk_A @ sk_B_1) = (k5_xboole_0 @ sk_A @ sk_B_1))),
% 0.25/0.59      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.25/0.59  thf('56', plain,
% 0.25/0.59      (![X16 : $i, X17 : $i]:
% 0.25/0.59         ((k2_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ (k4_xboole_0 @ X16 @ X17))
% 0.25/0.59           = (X16))),
% 0.25/0.59      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.25/0.59  thf('57', plain,
% 0.25/0.59      (((k2_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B_1) @ 
% 0.25/0.59         (k5_xboole_0 @ sk_A @ sk_B_1)) = (sk_A))),
% 0.25/0.59      inference('sup+', [status(thm)], ['55', '56'])).
% 0.25/0.59  thf('58', plain,
% 0.25/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.25/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.25/0.59  thf('59', plain, (((k3_xboole_0 @ sk_B_1 @ sk_A) = (sk_B_1))),
% 0.25/0.59      inference('sup-', [status(thm)], ['44', '45'])).
% 0.25/0.59  thf('60', plain,
% 0.25/0.59      (((k2_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ sk_A @ sk_B_1)) = (sk_A))),
% 0.25/0.59      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.25/0.59  thf('61', plain,
% 0.25/0.59      (((k4_subset_1 @ sk_A @ sk_B_1 @ (k5_xboole_0 @ sk_A @ sk_B_1)) = (sk_A))),
% 0.25/0.59      inference('demod', [status(thm)], ['51', '60'])).
% 0.25/0.59  thf('62', plain,
% 0.25/0.59      (((k4_subset_1 @ sk_A @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.25/0.59         != (k2_subset_1 @ sk_A))),
% 0.25/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.59  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.25/0.59  thf('63', plain, (![X33 : $i]: ((k2_subset_1 @ X33) = (X33))),
% 0.25/0.59      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.25/0.59  thf('64', plain,
% 0.25/0.59      (((k4_subset_1 @ sk_A @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) != (sk_A))),
% 0.25/0.59      inference('demod', [status(thm)], ['62', '63'])).
% 0.25/0.59  thf('65', plain,
% 0.25/0.59      (((k4_xboole_0 @ sk_A @ sk_B_1) = (k5_xboole_0 @ sk_A @ sk_B_1))),
% 0.25/0.59      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.25/0.59  thf('66', plain,
% 0.25/0.59      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.25/0.59      inference('sup-', [status(thm)], ['0', '1'])).
% 0.25/0.59  thf('67', plain,
% 0.25/0.59      (((k3_subset_1 @ sk_A @ sk_B_1) = (k5_xboole_0 @ sk_A @ sk_B_1))),
% 0.25/0.59      inference('sup+', [status(thm)], ['65', '66'])).
% 0.25/0.59  thf('68', plain,
% 0.25/0.59      (((k4_subset_1 @ sk_A @ sk_B_1 @ (k5_xboole_0 @ sk_A @ sk_B_1)) != (sk_A))),
% 0.25/0.59      inference('demod', [status(thm)], ['64', '67'])).
% 0.25/0.59  thf('69', plain, ($false),
% 0.25/0.59      inference('simplify_reflect-', [status(thm)], ['61', '68'])).
% 0.25/0.59  
% 0.25/0.59  % SZS output end Refutation
% 0.25/0.59  
% 0.44/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
