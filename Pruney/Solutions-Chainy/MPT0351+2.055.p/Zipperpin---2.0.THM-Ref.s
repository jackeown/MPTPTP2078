%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zHMd3EDo1B

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:04 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 321 expanded)
%              Number of leaves         :   35 ( 117 expanded)
%              Depth                    :   17
%              Number of atoms          :  841 (2305 expanded)
%              Number of equality atoms :   84 ( 218 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t28_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) )
          = ( k2_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
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
    ! [X56: $i,X57: $i] :
      ( ~ ( m1_subset_1 @ X56 @ X57 )
      | ( r2_hidden @ X56 @ X57 )
      | ( v1_xboole_0 @ X57 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X61: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('4',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['2','3'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('5',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ X52 @ X51 )
      | ( r1_tarski @ X52 @ X50 )
      | ( X51
       != ( k1_zfmisc_1 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('6',plain,(
    ! [X50: $i,X52: $i] :
      ( ( r1_tarski @ X52 @ X50 )
      | ~ ( r2_hidden @ X52 @ ( k1_zfmisc_1 @ X50 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['4','6'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X54 @ X55 ) )
      = ( k2_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('13',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X20 @ X21 ) )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['9','13'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('16',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('17',plain,(
    ! [X60: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X60 ) @ ( k1_zfmisc_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('18',plain,(
    ! [X59: $i] :
      ( ( k2_subset_1 @ X59 )
      = X59 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('19',plain,(
    ! [X60: $i] :
      ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ X60 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( m1_subset_1 @ X56 @ X57 )
      | ( r2_hidden @ X56 @ X57 )
      | ( v1_xboole_0 @ X57 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X61: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X50: $i,X52: $i] :
      ( ( r1_tarski @ X52 @ X50 )
      | ~ ( r2_hidden @ X52 @ ( k1_zfmisc_1 @ X50 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('28',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('29',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X9 @ X11 ) @ ( k3_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('34',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('35',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','39'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('41',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('45',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf('46',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X9 @ X11 ) @ ( k3_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_A ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_A ) )
      = ( k3_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_B @ k1_xboole_0 )
      = ( k3_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['43','50'])).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('53',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('54',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( sk_B
      = ( k3_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['51','52','55'])).

thf('57',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_A ) ) )
      = ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_A ) ) )
      = ( k5_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['42','60'])).

thf('62',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','61'])).

thf('63',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['42','60'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('65',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('68',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( sk_A
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['63','72'])).

thf('74',plain,
    ( sk_A
    = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['62','73'])).

thf('75',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k2_subset_1 @ sk_A ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X59: $i] :
      ( ( k2_subset_1 @ X59 )
      = X59 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('77',plain,(
    ! [X59: $i] :
      ( ( k2_subset_1 @ X59 )
      = X59 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('78',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    ! [X60: $i] :
      ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ X60 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('80',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('81',plain,(
    ! [X62: $i,X63: $i,X64: $i] :
      ( ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ X63 ) )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ X63 ) )
      | ( ( k4_subset_1 @ X63 @ X62 @ X64 )
        = ( k2_xboole_0 @ X62 @ X64 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('82',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X54 @ X55 ) )
      = ( k2_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('83',plain,(
    ! [X62: $i,X63: $i,X64: $i] :
      ( ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ X63 ) )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ X63 ) )
      | ( ( k4_subset_1 @ X63 @ X62 @ X64 )
        = ( k3_tarski @ ( k2_tarski @ X62 @ X64 ) ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','84'])).

thf('86',plain,(
    ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) )
 != sk_A ),
    inference(demod,[status(thm)],['78','85'])).

thf('87',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['74','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zHMd3EDo1B
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:54:02 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.48/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.48/0.71  % Solved by: fo/fo7.sh
% 0.48/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.71  % done 633 iterations in 0.249s
% 0.48/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.48/0.71  % SZS output start Refutation
% 0.48/0.71  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.48/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.48/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.71  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.48/0.71  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.48/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.48/0.71  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.48/0.71  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.48/0.71  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.48/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.48/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.48/0.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.48/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.48/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.48/0.71  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.48/0.71  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.48/0.71  thf(t28_subset_1, conjecture,
% 0.48/0.71    (![A:$i,B:$i]:
% 0.48/0.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.71       ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ))).
% 0.48/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.71    (~( ![A:$i,B:$i]:
% 0.48/0.71        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.71          ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ) )),
% 0.48/0.71    inference('cnf.neg', [status(esa)], [t28_subset_1])).
% 0.48/0.71  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf(d2_subset_1, axiom,
% 0.48/0.71    (![A:$i,B:$i]:
% 0.48/0.71     ( ( ( v1_xboole_0 @ A ) =>
% 0.48/0.71         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.48/0.71       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.48/0.71         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.48/0.71  thf('1', plain,
% 0.48/0.71      (![X56 : $i, X57 : $i]:
% 0.48/0.71         (~ (m1_subset_1 @ X56 @ X57)
% 0.48/0.71          | (r2_hidden @ X56 @ X57)
% 0.48/0.71          | (v1_xboole_0 @ X57))),
% 0.48/0.71      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.48/0.71  thf('2', plain,
% 0.48/0.71      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.48/0.71        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.48/0.71      inference('sup-', [status(thm)], ['0', '1'])).
% 0.48/0.71  thf(fc1_subset_1, axiom,
% 0.48/0.71    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.48/0.71  thf('3', plain, (![X61 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X61))),
% 0.48/0.71      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.48/0.71  thf('4', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.71      inference('clc', [status(thm)], ['2', '3'])).
% 0.48/0.71  thf(d1_zfmisc_1, axiom,
% 0.48/0.71    (![A:$i,B:$i]:
% 0.48/0.71     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.48/0.71       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.48/0.71  thf('5', plain,
% 0.48/0.71      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.48/0.71         (~ (r2_hidden @ X52 @ X51)
% 0.48/0.71          | (r1_tarski @ X52 @ X50)
% 0.48/0.71          | ((X51) != (k1_zfmisc_1 @ X50)))),
% 0.48/0.71      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.48/0.71  thf('6', plain,
% 0.48/0.71      (![X50 : $i, X52 : $i]:
% 0.48/0.71         ((r1_tarski @ X52 @ X50) | ~ (r2_hidden @ X52 @ (k1_zfmisc_1 @ X50)))),
% 0.48/0.71      inference('simplify', [status(thm)], ['5'])).
% 0.48/0.71  thf('7', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.48/0.71      inference('sup-', [status(thm)], ['4', '6'])).
% 0.48/0.71  thf(t28_xboole_1, axiom,
% 0.48/0.71    (![A:$i,B:$i]:
% 0.48/0.71     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.48/0.71  thf('8', plain,
% 0.48/0.71      (![X12 : $i, X13 : $i]:
% 0.48/0.71         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.48/0.71      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.48/0.71  thf('9', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.48/0.71      inference('sup-', [status(thm)], ['7', '8'])).
% 0.48/0.71  thf(t94_xboole_1, axiom,
% 0.48/0.71    (![A:$i,B:$i]:
% 0.48/0.71     ( ( k2_xboole_0 @ A @ B ) =
% 0.48/0.71       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.48/0.71  thf('10', plain,
% 0.48/0.71      (![X20 : $i, X21 : $i]:
% 0.48/0.71         ((k2_xboole_0 @ X20 @ X21)
% 0.48/0.71           = (k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ 
% 0.48/0.71              (k3_xboole_0 @ X20 @ X21)))),
% 0.48/0.71      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.48/0.71  thf(l51_zfmisc_1, axiom,
% 0.48/0.71    (![A:$i,B:$i]:
% 0.48/0.71     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.48/0.71  thf('11', plain,
% 0.48/0.71      (![X54 : $i, X55 : $i]:
% 0.48/0.71         ((k3_tarski @ (k2_tarski @ X54 @ X55)) = (k2_xboole_0 @ X54 @ X55))),
% 0.48/0.71      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.48/0.71  thf(t91_xboole_1, axiom,
% 0.48/0.71    (![A:$i,B:$i,C:$i]:
% 0.48/0.71     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.48/0.71       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.48/0.71  thf('12', plain,
% 0.48/0.71      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.48/0.71         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.48/0.71           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.48/0.71      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.48/0.71  thf('13', plain,
% 0.48/0.71      (![X20 : $i, X21 : $i]:
% 0.48/0.71         ((k3_tarski @ (k2_tarski @ X20 @ X21))
% 0.48/0.71           = (k5_xboole_0 @ X20 @ 
% 0.48/0.71              (k5_xboole_0 @ X21 @ (k3_xboole_0 @ X20 @ X21))))),
% 0.48/0.71      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.48/0.71  thf('14', plain,
% 0.48/0.71      (((k3_tarski @ (k2_tarski @ sk_B @ sk_A))
% 0.48/0.71         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 0.48/0.71      inference('sup+', [status(thm)], ['9', '13'])).
% 0.48/0.71  thf(commutativity_k5_xboole_0, axiom,
% 0.48/0.71    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.48/0.71  thf('15', plain,
% 0.48/0.71      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.48/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.48/0.71  thf('16', plain,
% 0.48/0.71      (((k3_tarski @ (k2_tarski @ sk_B @ sk_A))
% 0.48/0.71         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_A)))),
% 0.48/0.71      inference('demod', [status(thm)], ['14', '15'])).
% 0.48/0.71  thf(dt_k2_subset_1, axiom,
% 0.48/0.71    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.48/0.71  thf('17', plain,
% 0.48/0.71      (![X60 : $i]: (m1_subset_1 @ (k2_subset_1 @ X60) @ (k1_zfmisc_1 @ X60))),
% 0.48/0.71      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.48/0.71  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.48/0.71  thf('18', plain, (![X59 : $i]: ((k2_subset_1 @ X59) = (X59))),
% 0.48/0.71      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.48/0.71  thf('19', plain, (![X60 : $i]: (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ X60))),
% 0.48/0.71      inference('demod', [status(thm)], ['17', '18'])).
% 0.48/0.71  thf('20', plain,
% 0.48/0.71      (![X56 : $i, X57 : $i]:
% 0.48/0.71         (~ (m1_subset_1 @ X56 @ X57)
% 0.48/0.71          | (r2_hidden @ X56 @ X57)
% 0.48/0.71          | (v1_xboole_0 @ X57))),
% 0.48/0.71      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.48/0.71  thf('21', plain,
% 0.48/0.71      (![X0 : $i]:
% 0.48/0.71         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.48/0.71          | (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0)))),
% 0.48/0.71      inference('sup-', [status(thm)], ['19', '20'])).
% 0.48/0.71  thf('22', plain, (![X61 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X61))),
% 0.48/0.71      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.48/0.71  thf('23', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.48/0.71      inference('clc', [status(thm)], ['21', '22'])).
% 0.48/0.71  thf('24', plain,
% 0.48/0.71      (![X50 : $i, X52 : $i]:
% 0.48/0.71         ((r1_tarski @ X52 @ X50) | ~ (r2_hidden @ X52 @ (k1_zfmisc_1 @ X50)))),
% 0.48/0.71      inference('simplify', [status(thm)], ['5'])).
% 0.48/0.71  thf('25', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.48/0.71      inference('sup-', [status(thm)], ['23', '24'])).
% 0.48/0.71  thf('26', plain,
% 0.48/0.71      (![X12 : $i, X13 : $i]:
% 0.48/0.71         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.48/0.71      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.48/0.71  thf('27', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.48/0.71      inference('sup-', [status(thm)], ['25', '26'])).
% 0.48/0.71  thf(t100_xboole_1, axiom,
% 0.48/0.71    (![A:$i,B:$i]:
% 0.48/0.71     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.48/0.71  thf('28', plain,
% 0.48/0.71      (![X7 : $i, X8 : $i]:
% 0.48/0.71         ((k4_xboole_0 @ X7 @ X8)
% 0.48/0.71           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.48/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.48/0.71  thf(t112_xboole_1, axiom,
% 0.48/0.71    (![A:$i,B:$i,C:$i]:
% 0.48/0.71     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 0.48/0.71       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 0.48/0.71  thf('29', plain,
% 0.48/0.71      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.48/0.71         ((k5_xboole_0 @ (k3_xboole_0 @ X9 @ X11) @ (k3_xboole_0 @ X10 @ X11))
% 0.48/0.71           = (k3_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ X11))),
% 0.48/0.71      inference('cnf', [status(esa)], [t112_xboole_1])).
% 0.48/0.71  thf('30', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]:
% 0.48/0.71         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.48/0.71           = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.48/0.71      inference('sup+', [status(thm)], ['28', '29'])).
% 0.48/0.71  thf('31', plain,
% 0.48/0.71      (![X7 : $i, X8 : $i]:
% 0.48/0.71         ((k4_xboole_0 @ X7 @ X8)
% 0.48/0.71           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.48/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.48/0.71  thf(commutativity_k3_xboole_0, axiom,
% 0.48/0.71    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.48/0.71  thf('32', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.48/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.48/0.71  thf('33', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]:
% 0.48/0.71         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.48/0.71           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.48/0.71      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.48/0.71  thf(t79_xboole_1, axiom,
% 0.48/0.71    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.48/0.71  thf('34', plain,
% 0.48/0.71      (![X15 : $i, X16 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X16)),
% 0.48/0.71      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.48/0.71  thf(d7_xboole_0, axiom,
% 0.48/0.71    (![A:$i,B:$i]:
% 0.48/0.71     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.48/0.71       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.48/0.71  thf('35', plain,
% 0.48/0.71      (![X4 : $i, X5 : $i]:
% 0.48/0.71         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.48/0.71      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.48/0.71  thf('36', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]:
% 0.48/0.71         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.48/0.71      inference('sup-', [status(thm)], ['34', '35'])).
% 0.48/0.71  thf('37', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.48/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.48/0.71  thf('38', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]:
% 0.48/0.71         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.48/0.71      inference('demod', [status(thm)], ['36', '37'])).
% 0.48/0.71  thf('39', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]:
% 0.48/0.71         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.48/0.71      inference('demod', [status(thm)], ['33', '38'])).
% 0.48/0.71  thf('40', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.48/0.71      inference('sup+', [status(thm)], ['27', '39'])).
% 0.48/0.71  thf(t5_boole, axiom,
% 0.48/0.71    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.48/0.71  thf('41', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.48/0.71      inference('cnf', [status(esa)], [t5_boole])).
% 0.48/0.71  thf('42', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]:
% 0.48/0.71         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 0.48/0.71      inference('sup+', [status(thm)], ['40', '41'])).
% 0.48/0.71  thf('43', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]:
% 0.48/0.71         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.48/0.71      inference('demod', [status(thm)], ['36', '37'])).
% 0.48/0.71  thf('44', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.48/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.48/0.71  thf('45', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.48/0.71      inference('sup-', [status(thm)], ['7', '8'])).
% 0.48/0.71  thf('46', plain,
% 0.48/0.71      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.48/0.71         ((k5_xboole_0 @ (k3_xboole_0 @ X9 @ X11) @ (k3_xboole_0 @ X10 @ X11))
% 0.48/0.71           = (k3_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ X11))),
% 0.48/0.71      inference('cnf', [status(esa)], [t112_xboole_1])).
% 0.48/0.71  thf('47', plain,
% 0.48/0.71      (![X0 : $i]:
% 0.48/0.71         ((k5_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_A))
% 0.48/0.71           = (k3_xboole_0 @ (k5_xboole_0 @ sk_B @ X0) @ sk_A))),
% 0.48/0.71      inference('sup+', [status(thm)], ['45', '46'])).
% 0.48/0.71  thf('48', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.48/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.48/0.71  thf('49', plain,
% 0.48/0.71      (![X0 : $i]:
% 0.48/0.71         ((k5_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_A))
% 0.48/0.71           = (k3_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ X0)))),
% 0.48/0.71      inference('demod', [status(thm)], ['47', '48'])).
% 0.48/0.71  thf('50', plain,
% 0.48/0.71      (![X0 : $i]:
% 0.48/0.71         ((k5_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0))
% 0.48/0.71           = (k3_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ X0)))),
% 0.48/0.71      inference('sup+', [status(thm)], ['44', '49'])).
% 0.48/0.71  thf('51', plain,
% 0.48/0.71      (![X0 : $i]:
% 0.48/0.71         ((k5_xboole_0 @ sk_B @ k1_xboole_0)
% 0.48/0.71           = (k3_xboole_0 @ sk_A @ 
% 0.48/0.71              (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_A))))),
% 0.48/0.71      inference('sup+', [status(thm)], ['43', '50'])).
% 0.48/0.71  thf('52', plain,
% 0.48/0.71      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.48/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.48/0.71  thf('53', plain,
% 0.48/0.71      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.48/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.48/0.71  thf('54', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.48/0.71      inference('cnf', [status(esa)], [t5_boole])).
% 0.48/0.71  thf('55', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.48/0.71      inference('sup+', [status(thm)], ['53', '54'])).
% 0.48/0.71  thf('56', plain,
% 0.48/0.71      (![X0 : $i]:
% 0.48/0.71         ((sk_B)
% 0.48/0.71           = (k3_xboole_0 @ sk_A @ 
% 0.48/0.71              (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_A))))),
% 0.48/0.71      inference('demod', [status(thm)], ['51', '52', '55'])).
% 0.48/0.71  thf('57', plain,
% 0.48/0.71      (![X7 : $i, X8 : $i]:
% 0.48/0.71         ((k4_xboole_0 @ X7 @ X8)
% 0.48/0.71           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.48/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.48/0.71  thf('58', plain,
% 0.48/0.71      (![X0 : $i]:
% 0.48/0.71         ((k4_xboole_0 @ sk_A @ 
% 0.48/0.71           (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_A)))
% 0.48/0.71           = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.48/0.71      inference('sup+', [status(thm)], ['56', '57'])).
% 0.48/0.71  thf('59', plain,
% 0.48/0.71      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.48/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.48/0.71  thf('60', plain,
% 0.48/0.71      (![X0 : $i]:
% 0.48/0.71         ((k4_xboole_0 @ sk_A @ 
% 0.48/0.71           (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_A)))
% 0.48/0.71           = (k5_xboole_0 @ sk_B @ sk_A))),
% 0.48/0.71      inference('demod', [status(thm)], ['58', '59'])).
% 0.48/0.71  thf('61', plain,
% 0.48/0.71      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_B @ sk_A))),
% 0.48/0.71      inference('sup+', [status(thm)], ['42', '60'])).
% 0.48/0.71  thf('62', plain,
% 0.48/0.71      (((k3_tarski @ (k2_tarski @ sk_B @ sk_A))
% 0.48/0.71         = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.48/0.71      inference('demod', [status(thm)], ['16', '61'])).
% 0.48/0.71  thf('63', plain,
% 0.48/0.71      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_B @ sk_A))),
% 0.48/0.71      inference('sup+', [status(thm)], ['42', '60'])).
% 0.48/0.71  thf('64', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.48/0.71      inference('sup-', [status(thm)], ['25', '26'])).
% 0.48/0.71  thf('65', plain,
% 0.48/0.71      (![X7 : $i, X8 : $i]:
% 0.48/0.71         ((k4_xboole_0 @ X7 @ X8)
% 0.48/0.71           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.48/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.48/0.71  thf('66', plain,
% 0.48/0.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.48/0.71      inference('sup+', [status(thm)], ['64', '65'])).
% 0.48/0.71  thf('67', plain,
% 0.48/0.71      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.48/0.71         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.48/0.71           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.48/0.71      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.48/0.71  thf('68', plain,
% 0.48/0.71      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.48/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.48/0.71  thf('69', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.71         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.48/0.71           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.48/0.71      inference('sup+', [status(thm)], ['67', '68'])).
% 0.48/0.71  thf('70', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]:
% 0.48/0.71         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.48/0.71           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.48/0.71      inference('sup+', [status(thm)], ['66', '69'])).
% 0.48/0.71  thf('71', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]:
% 0.48/0.71         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 0.48/0.71      inference('sup+', [status(thm)], ['40', '41'])).
% 0.48/0.71  thf('72', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]:
% 0.48/0.71         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.48/0.71      inference('demod', [status(thm)], ['70', '71'])).
% 0.48/0.71  thf('73', plain,
% 0.48/0.71      (((sk_A) = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.48/0.71      inference('sup+', [status(thm)], ['63', '72'])).
% 0.48/0.71  thf('74', plain, (((sk_A) = (k3_tarski @ (k2_tarski @ sk_B @ sk_A)))),
% 0.48/0.71      inference('sup+', [status(thm)], ['62', '73'])).
% 0.48/0.71  thf('75', plain,
% 0.48/0.71      (((k4_subset_1 @ sk_A @ sk_B @ (k2_subset_1 @ sk_A))
% 0.48/0.71         != (k2_subset_1 @ sk_A))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('76', plain, (![X59 : $i]: ((k2_subset_1 @ X59) = (X59))),
% 0.48/0.71      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.48/0.71  thf('77', plain, (![X59 : $i]: ((k2_subset_1 @ X59) = (X59))),
% 0.48/0.71      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.48/0.71  thf('78', plain, (((k4_subset_1 @ sk_A @ sk_B @ sk_A) != (sk_A))),
% 0.48/0.71      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.48/0.71  thf('79', plain, (![X60 : $i]: (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ X60))),
% 0.48/0.71      inference('demod', [status(thm)], ['17', '18'])).
% 0.48/0.71  thf('80', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf(redefinition_k4_subset_1, axiom,
% 0.48/0.71    (![A:$i,B:$i,C:$i]:
% 0.48/0.71     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.48/0.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.48/0.71       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.48/0.71  thf('81', plain,
% 0.48/0.71      (![X62 : $i, X63 : $i, X64 : $i]:
% 0.48/0.71         (~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ X63))
% 0.48/0.71          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ X63))
% 0.48/0.71          | ((k4_subset_1 @ X63 @ X62 @ X64) = (k2_xboole_0 @ X62 @ X64)))),
% 0.48/0.71      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.48/0.71  thf('82', plain,
% 0.48/0.71      (![X54 : $i, X55 : $i]:
% 0.48/0.71         ((k3_tarski @ (k2_tarski @ X54 @ X55)) = (k2_xboole_0 @ X54 @ X55))),
% 0.48/0.71      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.48/0.71  thf('83', plain,
% 0.48/0.71      (![X62 : $i, X63 : $i, X64 : $i]:
% 0.48/0.71         (~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ X63))
% 0.48/0.71          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ X63))
% 0.48/0.71          | ((k4_subset_1 @ X63 @ X62 @ X64)
% 0.48/0.71              = (k3_tarski @ (k2_tarski @ X62 @ X64))))),
% 0.48/0.71      inference('demod', [status(thm)], ['81', '82'])).
% 0.48/0.71  thf('84', plain,
% 0.48/0.71      (![X0 : $i]:
% 0.48/0.71         (((k4_subset_1 @ sk_A @ sk_B @ X0)
% 0.48/0.71            = (k3_tarski @ (k2_tarski @ sk_B @ X0)))
% 0.48/0.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.48/0.71      inference('sup-', [status(thm)], ['80', '83'])).
% 0.48/0.71  thf('85', plain,
% 0.48/0.71      (((k4_subset_1 @ sk_A @ sk_B @ sk_A)
% 0.48/0.71         = (k3_tarski @ (k2_tarski @ sk_B @ sk_A)))),
% 0.48/0.71      inference('sup-', [status(thm)], ['79', '84'])).
% 0.48/0.71  thf('86', plain, (((k3_tarski @ (k2_tarski @ sk_B @ sk_A)) != (sk_A))),
% 0.48/0.71      inference('demod', [status(thm)], ['78', '85'])).
% 0.48/0.71  thf('87', plain, ($false),
% 0.48/0.71      inference('simplify_reflect-', [status(thm)], ['74', '86'])).
% 0.48/0.71  
% 0.48/0.71  % SZS output end Refutation
% 0.48/0.71  
% 0.48/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
