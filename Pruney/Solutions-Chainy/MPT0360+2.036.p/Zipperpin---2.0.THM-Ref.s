%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m0PlkcK0JE

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:45 EST 2020

% Result     : Theorem 3.77s
% Output     : Refutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 410 expanded)
%              Number of leaves         :   38 ( 136 expanded)
%              Depth                    :   19
%              Number of atoms          :  730 (3131 expanded)
%              Number of equality atoms :   42 ( 191 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(t40_subset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( ( r1_tarski @ B @ C )
          & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) )
       => ( B = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
       => ( ( ( r1_tarski @ B @ C )
            & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) )
         => ( B = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t40_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X73: $i,X74: $i] :
      ( ~ ( m1_subset_1 @ X73 @ X74 )
      | ( r2_hidden @ X73 @ X74 )
      | ( v1_xboole_0 @ X74 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('3',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ~ ( r2_hidden @ X57 @ X56 )
      | ( r1_tarski @ X57 @ X55 )
      | ( X56
       != ( k1_zfmisc_1 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('4',plain,(
    ! [X55: $i,X57: $i] :
      ( ( r1_tarski @ X57 @ X55 )
      | ~ ( r2_hidden @ X57 @ ( k1_zfmisc_1 @ X55 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r1_tarski @ sk_C_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    r1_tarski @ sk_B_2 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_2 @ X0 )
      | ~ ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r1_tarski @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X74: $i,X75: $i] :
      ( ~ ( m1_subset_1 @ X75 @ X74 )
      | ( v1_xboole_0 @ X75 )
      | ~ ( v1_xboole_0 @ X74 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('12',plain,
    ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r1_tarski @ sk_B_2 @ sk_A )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('14',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('15',plain,(
    ! [X12: $i] :
      ( r1_tarski @ k1_xboole_0 @ X12 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_2 @ X0 )
      | ~ ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_C_2 )
      | ( r1_tarski @ sk_B_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ sk_B_2 @ sk_A ),
    inference(clc,[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ~ ( r1_tarski @ X54 @ X55 )
      | ( r2_hidden @ X54 @ X56 )
      | ( X56
       != ( k1_zfmisc_1 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('21',plain,(
    ! [X54: $i,X55: $i] :
      ( ( r2_hidden @ X54 @ ( k1_zfmisc_1 @ X55 ) )
      | ~ ( r1_tarski @ X54 @ X55 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    r2_hidden @ sk_B_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X73: $i,X74: $i] :
      ( ~ ( r2_hidden @ X73 @ X74 )
      | ( m1_subset_1 @ X73 @ X74 )
      | ( v1_xboole_0 @ X74 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('25',plain,(
    ! [X77: $i,X78: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X77 @ X78 ) @ ( k1_zfmisc_1 @ X77 ) )
      | ~ ( m1_subset_1 @ X78 @ ( k1_zfmisc_1 @ X77 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('26',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B_2 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('27',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X54: $i,X55: $i] :
      ( ( r2_hidden @ X54 @ ( k1_zfmisc_1 @ X55 ) )
      | ~ ( r1_tarski @ X54 @ X55 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('34',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('35',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('36',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('37',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('38',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('41',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['39','42'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('44',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X23: $i] :
      ( ( k4_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','45'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('47',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('48',plain,(
    ! [X68: $i,X69: $i,X70: $i] :
      ( ( X68 != X70 )
      | ~ ( r2_hidden @ X68 @ ( k4_xboole_0 @ X69 @ ( k1_tarski @ X70 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('49',plain,(
    ! [X69: $i,X70: $i] :
      ~ ( r2_hidden @ X70 @ ( k4_xboole_0 @ X69 @ ( k1_tarski @ X70 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','52'])).

thf('54',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B_2 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['26','53'])).

thf('55',plain,(
    ! [X77: $i,X78: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X77 @ X78 ) @ ( k1_zfmisc_1 @ X77 ) )
      | ~ ( m1_subset_1 @ X78 @ ( k1_zfmisc_1 @ X77 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('56',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_2 ) ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('58',plain,(
    ! [X79: $i,X80: $i] :
      ( ( ( k3_subset_1 @ X80 @ ( k3_subset_1 @ X80 @ X79 ) )
        = X79 )
      | ~ ( m1_subset_1 @ X79 @ ( k1_zfmisc_1 @ X80 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('59',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_2 ) )
      = sk_B_2 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','52'])).

thf('61',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_2 ) )
    = sk_B_2 ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['56','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('64',plain,(
    ! [X81: $i,X82: $i,X83: $i] :
      ( ~ ( m1_subset_1 @ X81 @ ( k1_zfmisc_1 @ X82 ) )
      | ~ ( r1_tarski @ X83 @ X81 )
      | ( r1_tarski @ ( k3_subset_1 @ X82 @ X81 ) @ ( k3_subset_1 @ X82 @ X83 ) )
      | ~ ( m1_subset_1 @ X83 @ ( k1_zfmisc_1 @ X82 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ~ ( r1_tarski @ sk_B_2 @ sk_C_2 )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    r1_tarski @ sk_B_2 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    r1_tarski @ sk_B_2 @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_2 @ X0 )
      | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    r1_tarski @ sk_B_2 @ ( k3_subset_1 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf(t38_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf('73',plain,(
    ! [X84: $i,X85: $i] :
      ( ~ ( r1_tarski @ X85 @ ( k3_subset_1 @ X84 @ X85 ) )
      | ( X85
        = ( k1_subset_1 @ X84 ) )
      | ~ ( m1_subset_1 @ X85 @ ( k1_zfmisc_1 @ X84 ) ) ) ),
    inference(cnf,[status(esa)],[t38_subset_1])).

thf('74',plain,
    ( ~ ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( sk_B_2
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['56','61'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('76',plain,(
    ! [X76: $i] :
      ( ( k1_subset_1 @ X76 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('77',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['77','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m0PlkcK0JE
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:49:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.20/0.34  % Running in FO mode
% 3.77/3.95  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.77/3.95  % Solved by: fo/fo7.sh
% 3.77/3.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.77/3.95  % done 9808 iterations in 3.506s
% 3.77/3.95  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.77/3.95  % SZS output start Refutation
% 3.77/3.95  thf(sk_A_type, type, sk_A: $i).
% 3.77/3.95  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.77/3.95  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.77/3.95  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 3.77/3.95  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.77/3.95  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.77/3.95  thf(sk_B_2_type, type, sk_B_2: $i).
% 3.77/3.95  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.77/3.95  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.77/3.95  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.77/3.95  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.77/3.95  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.77/3.95  thf(sk_C_2_type, type, sk_C_2: $i).
% 3.77/3.95  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.77/3.95  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.77/3.95  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 3.77/3.95  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.77/3.95  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 3.77/3.95  thf(t40_subset_1, conjecture,
% 3.77/3.95    (![A:$i,B:$i,C:$i]:
% 3.77/3.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 3.77/3.95       ( ( ( r1_tarski @ B @ C ) & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 3.77/3.95         ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.77/3.95  thf(zf_stmt_0, negated_conjecture,
% 3.77/3.95    (~( ![A:$i,B:$i,C:$i]:
% 3.77/3.95        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 3.77/3.95          ( ( ( r1_tarski @ B @ C ) & 
% 3.77/3.95              ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 3.77/3.95            ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 3.77/3.95    inference('cnf.neg', [status(esa)], [t40_subset_1])).
% 3.77/3.95  thf('0', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 3.77/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.95  thf(d2_subset_1, axiom,
% 3.77/3.95    (![A:$i,B:$i]:
% 3.77/3.95     ( ( ( v1_xboole_0 @ A ) =>
% 3.77/3.95         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 3.77/3.95       ( ( ~( v1_xboole_0 @ A ) ) =>
% 3.77/3.95         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 3.77/3.95  thf('1', plain,
% 3.77/3.95      (![X73 : $i, X74 : $i]:
% 3.77/3.95         (~ (m1_subset_1 @ X73 @ X74)
% 3.77/3.95          | (r2_hidden @ X73 @ X74)
% 3.77/3.95          | (v1_xboole_0 @ X74))),
% 3.77/3.95      inference('cnf', [status(esa)], [d2_subset_1])).
% 3.77/3.95  thf('2', plain,
% 3.77/3.95      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 3.77/3.95        | (r2_hidden @ sk_C_2 @ (k1_zfmisc_1 @ sk_A)))),
% 3.77/3.95      inference('sup-', [status(thm)], ['0', '1'])).
% 3.77/3.95  thf(d1_zfmisc_1, axiom,
% 3.77/3.95    (![A:$i,B:$i]:
% 3.77/3.95     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 3.77/3.95       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 3.77/3.95  thf('3', plain,
% 3.77/3.95      (![X55 : $i, X56 : $i, X57 : $i]:
% 3.77/3.95         (~ (r2_hidden @ X57 @ X56)
% 3.77/3.95          | (r1_tarski @ X57 @ X55)
% 3.77/3.95          | ((X56) != (k1_zfmisc_1 @ X55)))),
% 3.77/3.95      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 3.77/3.95  thf('4', plain,
% 3.77/3.95      (![X55 : $i, X57 : $i]:
% 3.77/3.95         ((r1_tarski @ X57 @ X55) | ~ (r2_hidden @ X57 @ (k1_zfmisc_1 @ X55)))),
% 3.77/3.95      inference('simplify', [status(thm)], ['3'])).
% 3.77/3.95  thf('5', plain,
% 3.77/3.95      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A)) | (r1_tarski @ sk_C_2 @ sk_A))),
% 3.77/3.95      inference('sup-', [status(thm)], ['2', '4'])).
% 3.77/3.95  thf('6', plain, ((r1_tarski @ sk_B_2 @ sk_C_2)),
% 3.77/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.95  thf(t1_xboole_1, axiom,
% 3.77/3.95    (![A:$i,B:$i,C:$i]:
% 3.77/3.95     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 3.77/3.95       ( r1_tarski @ A @ C ) ))).
% 3.77/3.95  thf('7', plain,
% 3.77/3.95      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.77/3.95         (~ (r1_tarski @ X9 @ X10)
% 3.77/3.95          | ~ (r1_tarski @ X10 @ X11)
% 3.77/3.95          | (r1_tarski @ X9 @ X11))),
% 3.77/3.95      inference('cnf', [status(esa)], [t1_xboole_1])).
% 3.77/3.95  thf('8', plain,
% 3.77/3.95      (![X0 : $i]: ((r1_tarski @ sk_B_2 @ X0) | ~ (r1_tarski @ sk_C_2 @ X0))),
% 3.77/3.95      inference('sup-', [status(thm)], ['6', '7'])).
% 3.77/3.95  thf('9', plain,
% 3.77/3.95      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A)) | (r1_tarski @ sk_B_2 @ sk_A))),
% 3.77/3.95      inference('sup-', [status(thm)], ['5', '8'])).
% 3.77/3.95  thf('10', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 3.77/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.95  thf('11', plain,
% 3.77/3.95      (![X74 : $i, X75 : $i]:
% 3.77/3.95         (~ (m1_subset_1 @ X75 @ X74)
% 3.77/3.95          | (v1_xboole_0 @ X75)
% 3.77/3.95          | ~ (v1_xboole_0 @ X74))),
% 3.77/3.95      inference('cnf', [status(esa)], [d2_subset_1])).
% 3.77/3.95  thf('12', plain,
% 3.77/3.95      ((~ (v1_xboole_0 @ (k1_zfmisc_1 @ sk_A)) | (v1_xboole_0 @ sk_C_2))),
% 3.77/3.95      inference('sup-', [status(thm)], ['10', '11'])).
% 3.77/3.95  thf('13', plain, (((r1_tarski @ sk_B_2 @ sk_A) | (v1_xboole_0 @ sk_C_2))),
% 3.77/3.95      inference('sup-', [status(thm)], ['9', '12'])).
% 3.77/3.95  thf(l13_xboole_0, axiom,
% 3.77/3.95    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 3.77/3.95  thf('14', plain,
% 3.77/3.95      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X5))),
% 3.77/3.95      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.77/3.95  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 3.77/3.95  thf('15', plain, (![X12 : $i]: (r1_tarski @ k1_xboole_0 @ X12)),
% 3.77/3.95      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.77/3.95  thf('16', plain,
% 3.77/3.95      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 3.77/3.95      inference('sup+', [status(thm)], ['14', '15'])).
% 3.77/3.95  thf('17', plain,
% 3.77/3.95      (![X0 : $i]: ((r1_tarski @ sk_B_2 @ X0) | ~ (r1_tarski @ sk_C_2 @ X0))),
% 3.77/3.95      inference('sup-', [status(thm)], ['6', '7'])).
% 3.77/3.95  thf('18', plain,
% 3.77/3.95      (![X0 : $i]: (~ (v1_xboole_0 @ sk_C_2) | (r1_tarski @ sk_B_2 @ X0))),
% 3.77/3.95      inference('sup-', [status(thm)], ['16', '17'])).
% 3.77/3.95  thf('19', plain, ((r1_tarski @ sk_B_2 @ sk_A)),
% 3.77/3.95      inference('clc', [status(thm)], ['13', '18'])).
% 3.77/3.95  thf('20', plain,
% 3.77/3.95      (![X54 : $i, X55 : $i, X56 : $i]:
% 3.77/3.95         (~ (r1_tarski @ X54 @ X55)
% 3.77/3.95          | (r2_hidden @ X54 @ X56)
% 3.77/3.95          | ((X56) != (k1_zfmisc_1 @ X55)))),
% 3.77/3.95      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 3.77/3.95  thf('21', plain,
% 3.77/3.95      (![X54 : $i, X55 : $i]:
% 3.77/3.95         ((r2_hidden @ X54 @ (k1_zfmisc_1 @ X55)) | ~ (r1_tarski @ X54 @ X55))),
% 3.77/3.95      inference('simplify', [status(thm)], ['20'])).
% 3.77/3.95  thf('22', plain, ((r2_hidden @ sk_B_2 @ (k1_zfmisc_1 @ sk_A))),
% 3.77/3.95      inference('sup-', [status(thm)], ['19', '21'])).
% 3.77/3.95  thf('23', plain,
% 3.77/3.95      (![X73 : $i, X74 : $i]:
% 3.77/3.95         (~ (r2_hidden @ X73 @ X74)
% 3.77/3.95          | (m1_subset_1 @ X73 @ X74)
% 3.77/3.95          | (v1_xboole_0 @ X74))),
% 3.77/3.95      inference('cnf', [status(esa)], [d2_subset_1])).
% 3.77/3.95  thf('24', plain,
% 3.77/3.95      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 3.77/3.95        | (m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ sk_A)))),
% 3.77/3.95      inference('sup-', [status(thm)], ['22', '23'])).
% 3.77/3.95  thf(dt_k3_subset_1, axiom,
% 3.77/3.95    (![A:$i,B:$i]:
% 3.77/3.95     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.77/3.95       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 3.77/3.95  thf('25', plain,
% 3.77/3.95      (![X77 : $i, X78 : $i]:
% 3.77/3.95         ((m1_subset_1 @ (k3_subset_1 @ X77 @ X78) @ (k1_zfmisc_1 @ X77))
% 3.77/3.95          | ~ (m1_subset_1 @ X78 @ (k1_zfmisc_1 @ X77)))),
% 3.77/3.95      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 3.77/3.95  thf('26', plain,
% 3.77/3.95      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 3.77/3.95        | (m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B_2) @ (k1_zfmisc_1 @ sk_A)))),
% 3.77/3.95      inference('sup-', [status(thm)], ['24', '25'])).
% 3.77/3.95  thf(d3_tarski, axiom,
% 3.77/3.95    (![A:$i,B:$i]:
% 3.77/3.95     ( ( r1_tarski @ A @ B ) <=>
% 3.77/3.95       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 3.77/3.95  thf('27', plain,
% 3.77/3.95      (![X1 : $i, X3 : $i]:
% 3.77/3.95         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 3.77/3.95      inference('cnf', [status(esa)], [d3_tarski])).
% 3.77/3.95  thf('28', plain,
% 3.77/3.95      (![X1 : $i, X3 : $i]:
% 3.77/3.95         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 3.77/3.95      inference('cnf', [status(esa)], [d3_tarski])).
% 3.77/3.95  thf('29', plain,
% 3.77/3.95      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 3.77/3.95      inference('sup-', [status(thm)], ['27', '28'])).
% 3.77/3.95  thf('30', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 3.77/3.95      inference('simplify', [status(thm)], ['29'])).
% 3.77/3.95  thf('31', plain,
% 3.77/3.95      (![X54 : $i, X55 : $i]:
% 3.77/3.95         ((r2_hidden @ X54 @ (k1_zfmisc_1 @ X55)) | ~ (r1_tarski @ X54 @ X55))),
% 3.77/3.95      inference('simplify', [status(thm)], ['20'])).
% 3.77/3.95  thf('32', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 3.77/3.95      inference('sup-', [status(thm)], ['30', '31'])).
% 3.77/3.95  thf('33', plain,
% 3.77/3.95      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X5))),
% 3.77/3.95      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.77/3.95  thf(t92_xboole_1, axiom,
% 3.77/3.95    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 3.77/3.95  thf('34', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 3.77/3.95      inference('cnf', [status(esa)], [t92_xboole_1])).
% 3.77/3.95  thf(idempotence_k2_xboole_0, axiom,
% 3.77/3.95    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 3.77/3.95  thf('35', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 3.77/3.95      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 3.77/3.95  thf(t95_xboole_1, axiom,
% 3.77/3.95    (![A:$i,B:$i]:
% 3.77/3.95     ( ( k3_xboole_0 @ A @ B ) =
% 3.77/3.95       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 3.77/3.95  thf('36', plain,
% 3.77/3.95      (![X24 : $i, X25 : $i]:
% 3.77/3.95         ((k3_xboole_0 @ X24 @ X25)
% 3.77/3.95           = (k5_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ 
% 3.77/3.95              (k2_xboole_0 @ X24 @ X25)))),
% 3.77/3.95      inference('cnf', [status(esa)], [t95_xboole_1])).
% 3.77/3.95  thf(t91_xboole_1, axiom,
% 3.77/3.95    (![A:$i,B:$i,C:$i]:
% 3.77/3.95     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 3.77/3.95       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 3.77/3.95  thf('37', plain,
% 3.77/3.95      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.77/3.95         ((k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ X22)
% 3.77/3.95           = (k5_xboole_0 @ X20 @ (k5_xboole_0 @ X21 @ X22)))),
% 3.77/3.95      inference('cnf', [status(esa)], [t91_xboole_1])).
% 3.77/3.95  thf('38', plain,
% 3.77/3.95      (![X24 : $i, X25 : $i]:
% 3.77/3.95         ((k3_xboole_0 @ X24 @ X25)
% 3.77/3.95           = (k5_xboole_0 @ X24 @ 
% 3.77/3.95              (k5_xboole_0 @ X25 @ (k2_xboole_0 @ X24 @ X25))))),
% 3.77/3.95      inference('demod', [status(thm)], ['36', '37'])).
% 3.77/3.95  thf('39', plain,
% 3.77/3.95      (![X0 : $i]:
% 3.77/3.95         ((k3_xboole_0 @ X0 @ X0)
% 3.77/3.95           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 3.77/3.95      inference('sup+', [status(thm)], ['35', '38'])).
% 3.77/3.95  thf('40', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 3.77/3.95      inference('cnf', [status(esa)], [t92_xboole_1])).
% 3.77/3.95  thf(t5_boole, axiom,
% 3.77/3.95    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 3.77/3.95  thf('41', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 3.77/3.95      inference('cnf', [status(esa)], [t5_boole])).
% 3.77/3.95  thf('42', plain,
% 3.77/3.95      (![X0 : $i, X1 : $i]:
% 3.77/3.95         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 3.77/3.95      inference('sup+', [status(thm)], ['40', '41'])).
% 3.77/3.95  thf('43', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 3.77/3.95      inference('demod', [status(thm)], ['39', '42'])).
% 3.77/3.95  thf(t100_xboole_1, axiom,
% 3.77/3.95    (![A:$i,B:$i]:
% 3.77/3.95     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 3.77/3.95  thf('44', plain,
% 3.77/3.95      (![X7 : $i, X8 : $i]:
% 3.77/3.95         ((k4_xboole_0 @ X7 @ X8)
% 3.77/3.95           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 3.77/3.95      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.77/3.95  thf('45', plain,
% 3.77/3.95      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 3.77/3.95      inference('sup+', [status(thm)], ['43', '44'])).
% 3.77/3.95  thf('46', plain, (![X23 : $i]: ((k4_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 3.77/3.95      inference('demod', [status(thm)], ['34', '45'])).
% 3.77/3.95  thf(t69_enumset1, axiom,
% 3.77/3.95    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 3.77/3.95  thf('47', plain,
% 3.77/3.95      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 3.77/3.95      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.77/3.95  thf(t64_zfmisc_1, axiom,
% 3.77/3.95    (![A:$i,B:$i,C:$i]:
% 3.77/3.95     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 3.77/3.95       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 3.77/3.95  thf('48', plain,
% 3.77/3.95      (![X68 : $i, X69 : $i, X70 : $i]:
% 3.77/3.95         (((X68) != (X70))
% 3.77/3.95          | ~ (r2_hidden @ X68 @ (k4_xboole_0 @ X69 @ (k1_tarski @ X70))))),
% 3.77/3.95      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 3.77/3.95  thf('49', plain,
% 3.77/3.95      (![X69 : $i, X70 : $i]:
% 3.77/3.95         ~ (r2_hidden @ X70 @ (k4_xboole_0 @ X69 @ (k1_tarski @ X70)))),
% 3.77/3.95      inference('simplify', [status(thm)], ['48'])).
% 3.77/3.95  thf('50', plain,
% 3.77/3.95      (![X0 : $i, X1 : $i]:
% 3.77/3.95         ~ (r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ (k2_tarski @ X0 @ X0)))),
% 3.77/3.95      inference('sup-', [status(thm)], ['47', '49'])).
% 3.77/3.95  thf('51', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 3.77/3.95      inference('sup-', [status(thm)], ['46', '50'])).
% 3.77/3.95  thf('52', plain,
% 3.77/3.95      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 3.77/3.95      inference('sup-', [status(thm)], ['33', '51'])).
% 3.77/3.95  thf('53', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 3.77/3.95      inference('sup-', [status(thm)], ['32', '52'])).
% 3.77/3.95  thf('54', plain,
% 3.77/3.95      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B_2) @ (k1_zfmisc_1 @ sk_A))),
% 3.77/3.95      inference('clc', [status(thm)], ['26', '53'])).
% 3.77/3.95  thf('55', plain,
% 3.77/3.95      (![X77 : $i, X78 : $i]:
% 3.77/3.95         ((m1_subset_1 @ (k3_subset_1 @ X77 @ X78) @ (k1_zfmisc_1 @ X77))
% 3.77/3.95          | ~ (m1_subset_1 @ X78 @ (k1_zfmisc_1 @ X77)))),
% 3.77/3.95      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 3.77/3.95  thf('56', plain,
% 3.77/3.95      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_2)) @ 
% 3.77/3.95        (k1_zfmisc_1 @ sk_A))),
% 3.77/3.95      inference('sup-', [status(thm)], ['54', '55'])).
% 3.77/3.95  thf('57', plain,
% 3.77/3.95      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 3.77/3.95        | (m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ sk_A)))),
% 3.77/3.95      inference('sup-', [status(thm)], ['22', '23'])).
% 3.77/3.95  thf(involutiveness_k3_subset_1, axiom,
% 3.77/3.95    (![A:$i,B:$i]:
% 3.77/3.95     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.77/3.95       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 3.77/3.95  thf('58', plain,
% 3.77/3.95      (![X79 : $i, X80 : $i]:
% 3.77/3.95         (((k3_subset_1 @ X80 @ (k3_subset_1 @ X80 @ X79)) = (X79))
% 3.77/3.95          | ~ (m1_subset_1 @ X79 @ (k1_zfmisc_1 @ X80)))),
% 3.77/3.95      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 3.77/3.95  thf('59', plain,
% 3.77/3.95      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 3.77/3.95        | ((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_2)) = (sk_B_2)))),
% 3.77/3.95      inference('sup-', [status(thm)], ['57', '58'])).
% 3.77/3.95  thf('60', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 3.77/3.95      inference('sup-', [status(thm)], ['32', '52'])).
% 3.77/3.95  thf('61', plain,
% 3.77/3.95      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_2)) = (sk_B_2))),
% 3.77/3.95      inference('clc', [status(thm)], ['59', '60'])).
% 3.77/3.95  thf('62', plain, ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ sk_A))),
% 3.77/3.95      inference('demod', [status(thm)], ['56', '61'])).
% 3.77/3.95  thf('63', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 3.77/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.95  thf(t31_subset_1, axiom,
% 3.77/3.95    (![A:$i,B:$i]:
% 3.77/3.95     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.77/3.95       ( ![C:$i]:
% 3.77/3.95         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 3.77/3.95           ( ( r1_tarski @ B @ C ) <=>
% 3.77/3.95             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 3.77/3.95  thf('64', plain,
% 3.77/3.95      (![X81 : $i, X82 : $i, X83 : $i]:
% 3.77/3.95         (~ (m1_subset_1 @ X81 @ (k1_zfmisc_1 @ X82))
% 3.77/3.95          | ~ (r1_tarski @ X83 @ X81)
% 3.77/3.95          | (r1_tarski @ (k3_subset_1 @ X82 @ X81) @ (k3_subset_1 @ X82 @ X83))
% 3.77/3.95          | ~ (m1_subset_1 @ X83 @ (k1_zfmisc_1 @ X82)))),
% 3.77/3.95      inference('cnf', [status(esa)], [t31_subset_1])).
% 3.77/3.95  thf('65', plain,
% 3.77/3.95      (![X0 : $i]:
% 3.77/3.95         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 3.77/3.95          | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 3.77/3.95             (k3_subset_1 @ sk_A @ X0))
% 3.77/3.95          | ~ (r1_tarski @ X0 @ sk_C_2))),
% 3.77/3.95      inference('sup-', [status(thm)], ['63', '64'])).
% 3.77/3.95  thf('66', plain,
% 3.77/3.95      ((~ (r1_tarski @ sk_B_2 @ sk_C_2)
% 3.77/3.95        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 3.77/3.95           (k3_subset_1 @ sk_A @ sk_B_2)))),
% 3.77/3.95      inference('sup-', [status(thm)], ['62', '65'])).
% 3.77/3.95  thf('67', plain, ((r1_tarski @ sk_B_2 @ sk_C_2)),
% 3.77/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.95  thf('68', plain,
% 3.77/3.95      ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 3.77/3.95        (k3_subset_1 @ sk_A @ sk_B_2))),
% 3.77/3.95      inference('demod', [status(thm)], ['66', '67'])).
% 3.77/3.95  thf('69', plain, ((r1_tarski @ sk_B_2 @ (k3_subset_1 @ sk_A @ sk_C_2))),
% 3.77/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.95  thf('70', plain,
% 3.77/3.95      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.77/3.95         (~ (r1_tarski @ X9 @ X10)
% 3.77/3.95          | ~ (r1_tarski @ X10 @ X11)
% 3.77/3.95          | (r1_tarski @ X9 @ X11))),
% 3.77/3.95      inference('cnf', [status(esa)], [t1_xboole_1])).
% 3.77/3.95  thf('71', plain,
% 3.77/3.95      (![X0 : $i]:
% 3.77/3.95         ((r1_tarski @ sk_B_2 @ X0)
% 3.77/3.95          | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ X0))),
% 3.77/3.95      inference('sup-', [status(thm)], ['69', '70'])).
% 3.77/3.95  thf('72', plain, ((r1_tarski @ sk_B_2 @ (k3_subset_1 @ sk_A @ sk_B_2))),
% 3.77/3.95      inference('sup-', [status(thm)], ['68', '71'])).
% 3.77/3.95  thf(t38_subset_1, axiom,
% 3.77/3.95    (![A:$i,B:$i]:
% 3.77/3.95     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.77/3.95       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 3.77/3.95         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 3.77/3.95  thf('73', plain,
% 3.77/3.95      (![X84 : $i, X85 : $i]:
% 3.77/3.95         (~ (r1_tarski @ X85 @ (k3_subset_1 @ X84 @ X85))
% 3.77/3.95          | ((X85) = (k1_subset_1 @ X84))
% 3.77/3.95          | ~ (m1_subset_1 @ X85 @ (k1_zfmisc_1 @ X84)))),
% 3.77/3.95      inference('cnf', [status(esa)], [t38_subset_1])).
% 3.77/3.95  thf('74', plain,
% 3.77/3.95      ((~ (m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ sk_A))
% 3.77/3.95        | ((sk_B_2) = (k1_subset_1 @ sk_A)))),
% 3.77/3.95      inference('sup-', [status(thm)], ['72', '73'])).
% 3.77/3.95  thf('75', plain, ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ sk_A))),
% 3.77/3.95      inference('demod', [status(thm)], ['56', '61'])).
% 3.77/3.95  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 3.77/3.95  thf('76', plain, (![X76 : $i]: ((k1_subset_1 @ X76) = (k1_xboole_0))),
% 3.77/3.95      inference('cnf', [status(esa)], [d3_subset_1])).
% 3.77/3.95  thf('77', plain, (((sk_B_2) = (k1_xboole_0))),
% 3.77/3.95      inference('demod', [status(thm)], ['74', '75', '76'])).
% 3.77/3.95  thf('78', plain, (((sk_B_2) != (k1_xboole_0))),
% 3.77/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.95  thf('79', plain, ($false),
% 3.77/3.95      inference('simplify_reflect-', [status(thm)], ['77', '78'])).
% 3.77/3.95  
% 3.77/3.95  % SZS output end Refutation
% 3.77/3.95  
% 3.77/3.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
