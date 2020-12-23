%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ARF6dYtVPV

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:52 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 346 expanded)
%              Number of leaves         :   38 ( 123 expanded)
%              Depth                    :   21
%              Number of atoms          : 1074 (2461 expanded)
%              Number of equality atoms :   97 ( 200 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ! [X64: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X64 ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('15',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf('19',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) @ X0 )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('24',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('25',plain,(
    r1_tarski @ sk_B @ sk_B ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('27',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('29',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf('31',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('32',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = ( k4_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_B ) @ X0 )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','33'])).

thf('35',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('36',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_B ) @ X0 )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('40',plain,(
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( r1_tarski @ X49 @ X50 )
      | ( r2_hidden @ X49 @ X51 )
      | ( X51
       != ( k1_zfmisc_1 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('47',plain,(
    ! [X49: $i,X50: $i] :
      ( ( r2_hidden @ X49 @ ( k1_zfmisc_1 @ X50 ) )
      | ~ ( r1_tarski @ X49 @ X50 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( r2_hidden @ X56 @ X57 )
      | ( m1_subset_1 @ X56 @ X57 )
      | ( v1_xboole_0 @ X57 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X64: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('53',plain,(
    ! [X62: $i,X63: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X62 @ X63 ) @ ( k1_zfmisc_1 @ X62 ) )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('56',plain,(
    ! [X60: $i,X61: $i] :
      ( ( ( k3_subset_1 @ X60 @ X61 )
        = ( k4_xboole_0 @ X60 @ X61 ) )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('59',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('61',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['57','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','63'])).

thf('65',plain,(
    ! [X62: $i,X63: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X62 @ X63 ) @ ( k1_zfmisc_1 @ X62 ) )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','63'])).

thf('68',plain,(
    ! [X60: $i,X61: $i] :
      ( ( ( k3_subset_1 @ X60 @ X61 )
        = ( k4_xboole_0 @ X60 @ X61 ) )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( m1_subset_1 @ X56 @ X57 )
      | ( r2_hidden @ X56 @ X57 )
      | ( v1_xboole_0 @ X57 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X64: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X50: $i,X52: $i] :
      ( ( r1_tarski @ X52 @ X50 )
      | ~ ( r2_hidden @ X52 @ ( k1_zfmisc_1 @ X50 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('76',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('80',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('81',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['78','79','84'])).

thf('86',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('87',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['38','85','88'])).

thf('90',plain,
    ( sk_A
    = ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['17','89'])).

thf('91',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('93',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('94',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X54 @ X55 ) )
      = ( k2_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('95',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('96',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X20 @ X21 ) )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['92','96'])).

thf('98',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( sk_A
    = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['90','91','99'])).

thf('101',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('102',plain,(
    ! [X59: $i] :
      ( ( k2_subset_1 @ X59 )
      = X59 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('103',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X60: $i,X61: $i] :
      ( ( ( k3_subset_1 @ X60 @ X61 )
        = ( k4_xboole_0 @ X60 @ X61 ) )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('106',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['103','106'])).

thf('108',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X62: $i,X63: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X62 @ X63 ) @ ( k1_zfmisc_1 @ X62 ) )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('110',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('112',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('114',plain,(
    ! [X65: $i,X66: $i,X67: $i] :
      ( ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ X66 ) )
      | ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ X66 ) )
      | ( ( k4_subset_1 @ X66 @ X65 @ X67 )
        = ( k2_xboole_0 @ X65 @ X67 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('115',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X54 @ X55 ) )
      = ( k2_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('116',plain,(
    ! [X65: $i,X66: $i,X67: $i] :
      ( ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ X66 ) )
      | ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ X66 ) )
      | ( ( k4_subset_1 @ X66 @ X65 @ X67 )
        = ( k3_tarski @ ( k2_tarski @ X65 @ X67 ) ) ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['113','116'])).

thf('118',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['112','117'])).

thf('119',plain,(
    ( k3_tarski @ ( k2_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) )
 != sk_A ),
    inference(demod,[status(thm)],['107','118'])).

thf('120',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['100','119'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ARF6dYtVPV
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:44:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.53/0.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.53/0.72  % Solved by: fo/fo7.sh
% 0.53/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.72  % done 598 iterations in 0.257s
% 0.53/0.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.53/0.72  % SZS output start Refutation
% 0.53/0.72  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.53/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.72  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.53/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.72  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.53/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.53/0.72  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.53/0.72  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.53/0.72  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.53/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.53/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.53/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.72  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.53/0.72  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.53/0.72  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.53/0.72  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.53/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.72  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.53/0.72  thf(t25_subset_1, conjecture,
% 0.53/0.72    (![A:$i,B:$i]:
% 0.53/0.72     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.53/0.72       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.53/0.72         ( k2_subset_1 @ A ) ) ))).
% 0.53/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.72    (~( ![A:$i,B:$i]:
% 0.53/0.72        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.53/0.72          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.53/0.72            ( k2_subset_1 @ A ) ) ) )),
% 0.53/0.72    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 0.53/0.72  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf(d2_subset_1, axiom,
% 0.53/0.72    (![A:$i,B:$i]:
% 0.53/0.72     ( ( ( v1_xboole_0 @ A ) =>
% 0.53/0.72         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.53/0.72       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.53/0.72         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.53/0.72  thf('1', plain,
% 0.53/0.72      (![X56 : $i, X57 : $i]:
% 0.53/0.72         (~ (m1_subset_1 @ X56 @ X57)
% 0.53/0.72          | (r2_hidden @ X56 @ X57)
% 0.53/0.72          | (v1_xboole_0 @ X57))),
% 0.53/0.72      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.53/0.72  thf('2', plain,
% 0.53/0.72      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.53/0.72        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.53/0.72      inference('sup-', [status(thm)], ['0', '1'])).
% 0.53/0.72  thf(fc1_subset_1, axiom,
% 0.53/0.72    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.53/0.72  thf('3', plain, (![X64 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X64))),
% 0.53/0.72      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.53/0.72  thf('4', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.53/0.72      inference('clc', [status(thm)], ['2', '3'])).
% 0.53/0.72  thf(d1_zfmisc_1, axiom,
% 0.53/0.72    (![A:$i,B:$i]:
% 0.53/0.72     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.53/0.72       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.53/0.72  thf('5', plain,
% 0.53/0.72      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.53/0.72         (~ (r2_hidden @ X52 @ X51)
% 0.53/0.72          | (r1_tarski @ X52 @ X50)
% 0.53/0.72          | ((X51) != (k1_zfmisc_1 @ X50)))),
% 0.53/0.72      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.53/0.72  thf('6', plain,
% 0.53/0.72      (![X50 : $i, X52 : $i]:
% 0.53/0.72         ((r1_tarski @ X52 @ X50) | ~ (r2_hidden @ X52 @ (k1_zfmisc_1 @ X50)))),
% 0.53/0.72      inference('simplify', [status(thm)], ['5'])).
% 0.53/0.72  thf('7', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.53/0.72      inference('sup-', [status(thm)], ['4', '6'])).
% 0.53/0.72  thf(t28_xboole_1, axiom,
% 0.53/0.72    (![A:$i,B:$i]:
% 0.53/0.72     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.53/0.72  thf('8', plain,
% 0.53/0.72      (![X11 : $i, X12 : $i]:
% 0.53/0.72         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.53/0.72      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.53/0.72  thf('9', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.53/0.72      inference('sup-', [status(thm)], ['7', '8'])).
% 0.53/0.72  thf(commutativity_k3_xboole_0, axiom,
% 0.53/0.72    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.53/0.72  thf('10', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.53/0.72  thf(t100_xboole_1, axiom,
% 0.53/0.72    (![A:$i,B:$i]:
% 0.53/0.72     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.53/0.72  thf('11', plain,
% 0.53/0.72      (![X7 : $i, X8 : $i]:
% 0.53/0.72         ((k4_xboole_0 @ X7 @ X8)
% 0.53/0.72           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.53/0.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.53/0.72  thf('12', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         ((k4_xboole_0 @ X0 @ X1)
% 0.53/0.72           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.53/0.72      inference('sup+', [status(thm)], ['10', '11'])).
% 0.53/0.72  thf('13', plain,
% 0.53/0.72      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.53/0.72      inference('sup+', [status(thm)], ['9', '12'])).
% 0.53/0.72  thf(commutativity_k5_xboole_0, axiom,
% 0.53/0.72    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.53/0.72  thf('14', plain,
% 0.53/0.72      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.53/0.72      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.53/0.72  thf('15', plain,
% 0.53/0.72      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_B @ sk_A))),
% 0.53/0.72      inference('demod', [status(thm)], ['13', '14'])).
% 0.53/0.72  thf(t91_xboole_1, axiom,
% 0.53/0.72    (![A:$i,B:$i,C:$i]:
% 0.53/0.72     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.53/0.72       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.53/0.72  thf('16', plain,
% 0.53/0.72      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.53/0.72         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.53/0.72           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.53/0.72      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.53/0.72  thf('17', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((k5_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ X0)
% 0.53/0.72           = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ X0)))),
% 0.53/0.72      inference('sup+', [status(thm)], ['15', '16'])).
% 0.53/0.72  thf('18', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.53/0.72      inference('sup-', [status(thm)], ['7', '8'])).
% 0.53/0.72  thf('19', plain,
% 0.53/0.72      (![X7 : $i, X8 : $i]:
% 0.53/0.72         ((k4_xboole_0 @ X7 @ X8)
% 0.53/0.72           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.53/0.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.53/0.72  thf('20', plain,
% 0.53/0.72      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.53/0.72         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.53/0.72           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.53/0.72      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.53/0.72  thf('21', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.72         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.53/0.72           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 0.53/0.72      inference('sup+', [status(thm)], ['19', '20'])).
% 0.53/0.72  thf('22', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A) @ X0)
% 0.53/0.72           = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ X0)))),
% 0.53/0.72      inference('sup+', [status(thm)], ['18', '21'])).
% 0.53/0.72  thf('23', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.53/0.72      inference('sup-', [status(thm)], ['7', '8'])).
% 0.53/0.72  thf(t17_xboole_1, axiom,
% 0.53/0.72    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.53/0.72  thf('24', plain,
% 0.53/0.72      (![X9 : $i, X10 : $i]: (r1_tarski @ (k3_xboole_0 @ X9 @ X10) @ X9)),
% 0.53/0.72      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.53/0.72  thf('25', plain, ((r1_tarski @ sk_B @ sk_B)),
% 0.53/0.72      inference('sup+', [status(thm)], ['23', '24'])).
% 0.53/0.72  thf('26', plain,
% 0.53/0.72      (![X11 : $i, X12 : $i]:
% 0.53/0.72         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.53/0.72      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.53/0.72  thf('27', plain, (((k3_xboole_0 @ sk_B @ sk_B) = (sk_B))),
% 0.53/0.72      inference('sup-', [status(thm)], ['25', '26'])).
% 0.53/0.72  thf('28', plain,
% 0.53/0.72      (![X7 : $i, X8 : $i]:
% 0.53/0.72         ((k4_xboole_0 @ X7 @ X8)
% 0.53/0.72           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.53/0.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.53/0.72  thf('29', plain,
% 0.53/0.72      (((k4_xboole_0 @ sk_B @ sk_B) = (k5_xboole_0 @ sk_B @ sk_B))),
% 0.53/0.72      inference('sup+', [status(thm)], ['27', '28'])).
% 0.53/0.72  thf('30', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.53/0.72      inference('sup-', [status(thm)], ['7', '8'])).
% 0.53/0.72  thf('31', plain,
% 0.53/0.72      (![X7 : $i, X8 : $i]:
% 0.53/0.72         ((k4_xboole_0 @ X7 @ X8)
% 0.53/0.72           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.53/0.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.53/0.72  thf('32', plain,
% 0.53/0.72      (((k4_xboole_0 @ sk_B @ sk_A) = (k5_xboole_0 @ sk_B @ sk_B))),
% 0.53/0.72      inference('sup+', [status(thm)], ['30', '31'])).
% 0.53/0.72  thf('33', plain,
% 0.53/0.72      (((k4_xboole_0 @ sk_B @ sk_A) = (k4_xboole_0 @ sk_B @ sk_B))),
% 0.53/0.72      inference('sup+', [status(thm)], ['29', '32'])).
% 0.53/0.72  thf('34', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_B) @ X0)
% 0.53/0.72           = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ X0)))),
% 0.53/0.72      inference('demod', [status(thm)], ['22', '33'])).
% 0.53/0.72  thf('35', plain,
% 0.53/0.72      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.53/0.72         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.53/0.72           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.53/0.72      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.53/0.72  thf('36', plain,
% 0.53/0.72      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.53/0.72      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.53/0.72  thf('37', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.72         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.53/0.72           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.53/0.72      inference('sup+', [status(thm)], ['35', '36'])).
% 0.53/0.72  thf('38', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_B) @ X0)
% 0.53/0.72           = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ X0 @ sk_B)))),
% 0.53/0.72      inference('sup+', [status(thm)], ['34', '37'])).
% 0.53/0.72  thf('39', plain,
% 0.53/0.72      (![X9 : $i, X10 : $i]: (r1_tarski @ (k3_xboole_0 @ X9 @ X10) @ X9)),
% 0.53/0.72      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.53/0.72  thf(t3_xboole_1, axiom,
% 0.53/0.72    (![A:$i]:
% 0.53/0.72     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.53/0.72  thf('40', plain,
% 0.53/0.72      (![X13 : $i]:
% 0.53/0.72         (((X13) = (k1_xboole_0)) | ~ (r1_tarski @ X13 @ k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.53/0.72  thf('41', plain,
% 0.53/0.72      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.53/0.72      inference('sup-', [status(thm)], ['39', '40'])).
% 0.53/0.72  thf('42', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.53/0.72  thf('43', plain,
% 0.53/0.72      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.72      inference('sup+', [status(thm)], ['41', '42'])).
% 0.53/0.72  thf('44', plain,
% 0.53/0.72      (![X9 : $i, X10 : $i]: (r1_tarski @ (k3_xboole_0 @ X9 @ X10) @ X9)),
% 0.53/0.72      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.53/0.72  thf('45', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.53/0.72      inference('sup+', [status(thm)], ['43', '44'])).
% 0.53/0.72  thf('46', plain,
% 0.53/0.72      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.53/0.72         (~ (r1_tarski @ X49 @ X50)
% 0.53/0.72          | (r2_hidden @ X49 @ X51)
% 0.53/0.72          | ((X51) != (k1_zfmisc_1 @ X50)))),
% 0.53/0.72      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.53/0.72  thf('47', plain,
% 0.53/0.72      (![X49 : $i, X50 : $i]:
% 0.53/0.72         ((r2_hidden @ X49 @ (k1_zfmisc_1 @ X50)) | ~ (r1_tarski @ X49 @ X50))),
% 0.53/0.72      inference('simplify', [status(thm)], ['46'])).
% 0.53/0.72  thf('48', plain,
% 0.53/0.72      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.53/0.72      inference('sup-', [status(thm)], ['45', '47'])).
% 0.53/0.72  thf('49', plain,
% 0.53/0.72      (![X56 : $i, X57 : $i]:
% 0.53/0.72         (~ (r2_hidden @ X56 @ X57)
% 0.53/0.72          | (m1_subset_1 @ X56 @ X57)
% 0.53/0.72          | (v1_xboole_0 @ X57))),
% 0.53/0.72      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.53/0.72  thf('50', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.53/0.72          | (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 0.53/0.72      inference('sup-', [status(thm)], ['48', '49'])).
% 0.53/0.72  thf('51', plain, (![X64 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X64))),
% 0.53/0.72      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.53/0.72  thf('52', plain,
% 0.53/0.72      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.53/0.72      inference('clc', [status(thm)], ['50', '51'])).
% 0.53/0.72  thf(dt_k3_subset_1, axiom,
% 0.53/0.72    (![A:$i,B:$i]:
% 0.53/0.72     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.53/0.72       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.53/0.72  thf('53', plain,
% 0.53/0.72      (![X62 : $i, X63 : $i]:
% 0.53/0.72         ((m1_subset_1 @ (k3_subset_1 @ X62 @ X63) @ (k1_zfmisc_1 @ X62))
% 0.53/0.72          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ X62)))),
% 0.53/0.72      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.53/0.72  thf('54', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (m1_subset_1 @ (k3_subset_1 @ X0 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.53/0.72      inference('sup-', [status(thm)], ['52', '53'])).
% 0.53/0.72  thf('55', plain,
% 0.53/0.72      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.53/0.72      inference('clc', [status(thm)], ['50', '51'])).
% 0.53/0.72  thf(d5_subset_1, axiom,
% 0.53/0.72    (![A:$i,B:$i]:
% 0.53/0.72     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.53/0.72       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.53/0.72  thf('56', plain,
% 0.53/0.72      (![X60 : $i, X61 : $i]:
% 0.53/0.72         (((k3_subset_1 @ X60 @ X61) = (k4_xboole_0 @ X60 @ X61))
% 0.53/0.72          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ X60)))),
% 0.53/0.72      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.53/0.72  thf('57', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.53/0.72      inference('sup-', [status(thm)], ['55', '56'])).
% 0.53/0.72  thf('58', plain,
% 0.53/0.72      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.72      inference('sup+', [status(thm)], ['41', '42'])).
% 0.53/0.72  thf('59', plain,
% 0.53/0.72      (![X7 : $i, X8 : $i]:
% 0.53/0.72         ((k4_xboole_0 @ X7 @ X8)
% 0.53/0.72           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.53/0.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.53/0.72  thf('60', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.53/0.72      inference('sup+', [status(thm)], ['58', '59'])).
% 0.53/0.72  thf(t5_boole, axiom,
% 0.53/0.72    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.53/0.72  thf('61', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.53/0.72      inference('cnf', [status(esa)], [t5_boole])).
% 0.53/0.72  thf('62', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.53/0.72      inference('sup+', [status(thm)], ['60', '61'])).
% 0.53/0.72  thf('63', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.53/0.72      inference('demod', [status(thm)], ['57', '62'])).
% 0.53/0.72  thf('64', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.53/0.72      inference('demod', [status(thm)], ['54', '63'])).
% 0.53/0.72  thf('65', plain,
% 0.53/0.72      (![X62 : $i, X63 : $i]:
% 0.53/0.72         ((m1_subset_1 @ (k3_subset_1 @ X62 @ X63) @ (k1_zfmisc_1 @ X62))
% 0.53/0.72          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ X62)))),
% 0.53/0.72      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.53/0.72  thf('66', plain,
% 0.53/0.72      (![X0 : $i]: (m1_subset_1 @ (k3_subset_1 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.53/0.72      inference('sup-', [status(thm)], ['64', '65'])).
% 0.53/0.72  thf('67', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.53/0.72      inference('demod', [status(thm)], ['54', '63'])).
% 0.53/0.72  thf('68', plain,
% 0.53/0.72      (![X60 : $i, X61 : $i]:
% 0.53/0.72         (((k3_subset_1 @ X60 @ X61) = (k4_xboole_0 @ X60 @ X61))
% 0.53/0.72          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ X60)))),
% 0.53/0.72      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.53/0.72  thf('69', plain,
% 0.53/0.72      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.53/0.72      inference('sup-', [status(thm)], ['67', '68'])).
% 0.53/0.72  thf('70', plain,
% 0.53/0.72      (![X0 : $i]: (m1_subset_1 @ (k4_xboole_0 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.53/0.72      inference('demod', [status(thm)], ['66', '69'])).
% 0.53/0.72  thf('71', plain,
% 0.53/0.72      (![X56 : $i, X57 : $i]:
% 0.53/0.72         (~ (m1_subset_1 @ X56 @ X57)
% 0.53/0.72          | (r2_hidden @ X56 @ X57)
% 0.53/0.72          | (v1_xboole_0 @ X57))),
% 0.53/0.72      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.53/0.72  thf('72', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.53/0.72          | (r2_hidden @ (k4_xboole_0 @ X0 @ X0) @ (k1_zfmisc_1 @ X0)))),
% 0.53/0.72      inference('sup-', [status(thm)], ['70', '71'])).
% 0.53/0.72  thf('73', plain, (![X64 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X64))),
% 0.53/0.72      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.53/0.72  thf('74', plain,
% 0.53/0.72      (![X0 : $i]: (r2_hidden @ (k4_xboole_0 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.53/0.72      inference('clc', [status(thm)], ['72', '73'])).
% 0.53/0.72  thf('75', plain,
% 0.53/0.72      (![X50 : $i, X52 : $i]:
% 0.53/0.72         ((r1_tarski @ X52 @ X50) | ~ (r2_hidden @ X52 @ (k1_zfmisc_1 @ X50)))),
% 0.53/0.72      inference('simplify', [status(thm)], ['5'])).
% 0.53/0.72  thf('76', plain, (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X0)),
% 0.53/0.72      inference('sup-', [status(thm)], ['74', '75'])).
% 0.53/0.72  thf('77', plain,
% 0.53/0.72      (![X11 : $i, X12 : $i]:
% 0.53/0.72         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.53/0.72      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.53/0.72  thf('78', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0)
% 0.53/0.72           = (k4_xboole_0 @ X0 @ X0))),
% 0.53/0.72      inference('sup-', [status(thm)], ['76', '77'])).
% 0.53/0.72  thf('79', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.53/0.72  thf(t79_xboole_1, axiom,
% 0.53/0.72    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.53/0.72  thf('80', plain,
% 0.53/0.72      (![X15 : $i, X16 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X16)),
% 0.53/0.72      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.53/0.72  thf(d7_xboole_0, axiom,
% 0.53/0.72    (![A:$i,B:$i]:
% 0.53/0.72     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.53/0.72       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.53/0.72  thf('81', plain,
% 0.53/0.72      (![X4 : $i, X5 : $i]:
% 0.53/0.72         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.53/0.72      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.53/0.72  thf('82', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.53/0.72      inference('sup-', [status(thm)], ['80', '81'])).
% 0.53/0.72  thf('83', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.53/0.72  thf('84', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.53/0.72      inference('demod', [status(thm)], ['82', '83'])).
% 0.53/0.72  thf('85', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.53/0.72      inference('demod', [status(thm)], ['78', '79', '84'])).
% 0.53/0.72  thf('86', plain,
% 0.53/0.72      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.53/0.72      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.53/0.72  thf('87', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.53/0.72      inference('cnf', [status(esa)], [t5_boole])).
% 0.53/0.72  thf('88', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.53/0.72      inference('sup+', [status(thm)], ['86', '87'])).
% 0.53/0.72  thf('89', plain,
% 0.53/0.72      (![X0 : $i]: ((X0) = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ X0 @ sk_B)))),
% 0.53/0.72      inference('demod', [status(thm)], ['38', '85', '88'])).
% 0.53/0.72  thf('90', plain,
% 0.53/0.72      (((sk_A) = (k5_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B))),
% 0.53/0.72      inference('sup+', [status(thm)], ['17', '89'])).
% 0.53/0.72  thf('91', plain,
% 0.53/0.72      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.53/0.72      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.53/0.72  thf('92', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.53/0.72      inference('demod', [status(thm)], ['82', '83'])).
% 0.53/0.72  thf(t94_xboole_1, axiom,
% 0.53/0.72    (![A:$i,B:$i]:
% 0.53/0.72     ( ( k2_xboole_0 @ A @ B ) =
% 0.53/0.72       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.53/0.72  thf('93', plain,
% 0.53/0.72      (![X20 : $i, X21 : $i]:
% 0.53/0.72         ((k2_xboole_0 @ X20 @ X21)
% 0.53/0.72           = (k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ 
% 0.53/0.72              (k3_xboole_0 @ X20 @ X21)))),
% 0.53/0.72      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.53/0.72  thf(l51_zfmisc_1, axiom,
% 0.53/0.72    (![A:$i,B:$i]:
% 0.53/0.72     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.53/0.72  thf('94', plain,
% 0.53/0.72      (![X54 : $i, X55 : $i]:
% 0.53/0.72         ((k3_tarski @ (k2_tarski @ X54 @ X55)) = (k2_xboole_0 @ X54 @ X55))),
% 0.53/0.72      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.53/0.72  thf('95', plain,
% 0.53/0.72      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.53/0.72         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.53/0.72           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.53/0.72      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.53/0.72  thf('96', plain,
% 0.53/0.72      (![X20 : $i, X21 : $i]:
% 0.53/0.72         ((k3_tarski @ (k2_tarski @ X20 @ X21))
% 0.53/0.72           = (k5_xboole_0 @ X20 @ 
% 0.53/0.72              (k5_xboole_0 @ X21 @ (k3_xboole_0 @ X20 @ X21))))),
% 0.53/0.72      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.53/0.72  thf('97', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         ((k3_tarski @ (k2_tarski @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 0.53/0.72           = (k5_xboole_0 @ X0 @ 
% 0.53/0.72              (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0)))),
% 0.53/0.72      inference('sup+', [status(thm)], ['92', '96'])).
% 0.53/0.72  thf('98', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.53/0.72      inference('cnf', [status(esa)], [t5_boole])).
% 0.53/0.72  thf('99', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         ((k3_tarski @ (k2_tarski @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 0.53/0.72           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.53/0.72      inference('demod', [status(thm)], ['97', '98'])).
% 0.53/0.72  thf('100', plain,
% 0.53/0.72      (((sk_A) = (k3_tarski @ (k2_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))))),
% 0.53/0.72      inference('demod', [status(thm)], ['90', '91', '99'])).
% 0.53/0.72  thf('101', plain,
% 0.53/0.72      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.53/0.72         != (k2_subset_1 @ sk_A))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.53/0.72  thf('102', plain, (![X59 : $i]: ((k2_subset_1 @ X59) = (X59))),
% 0.53/0.72      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.53/0.72  thf('103', plain,
% 0.53/0.72      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.53/0.72      inference('demod', [status(thm)], ['101', '102'])).
% 0.53/0.72  thf('104', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('105', plain,
% 0.53/0.72      (![X60 : $i, X61 : $i]:
% 0.53/0.72         (((k3_subset_1 @ X60 @ X61) = (k4_xboole_0 @ X60 @ X61))
% 0.53/0.72          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ X60)))),
% 0.53/0.72      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.53/0.72  thf('106', plain,
% 0.53/0.72      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.53/0.72      inference('sup-', [status(thm)], ['104', '105'])).
% 0.53/0.72  thf('107', plain,
% 0.53/0.72      (((k4_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)) != (sk_A))),
% 0.53/0.72      inference('demod', [status(thm)], ['103', '106'])).
% 0.53/0.72  thf('108', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('109', plain,
% 0.53/0.72      (![X62 : $i, X63 : $i]:
% 0.53/0.72         ((m1_subset_1 @ (k3_subset_1 @ X62 @ X63) @ (k1_zfmisc_1 @ X62))
% 0.53/0.72          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ X62)))),
% 0.53/0.72      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.53/0.72  thf('110', plain,
% 0.53/0.72      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.53/0.72      inference('sup-', [status(thm)], ['108', '109'])).
% 0.53/0.72  thf('111', plain,
% 0.53/0.72      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.53/0.72      inference('sup-', [status(thm)], ['104', '105'])).
% 0.53/0.72  thf('112', plain,
% 0.53/0.72      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.53/0.72      inference('demod', [status(thm)], ['110', '111'])).
% 0.53/0.72  thf('113', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf(redefinition_k4_subset_1, axiom,
% 0.53/0.72    (![A:$i,B:$i,C:$i]:
% 0.53/0.72     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.53/0.72         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.53/0.72       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.53/0.72  thf('114', plain,
% 0.53/0.72      (![X65 : $i, X66 : $i, X67 : $i]:
% 0.53/0.72         (~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ X66))
% 0.53/0.72          | ~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ X66))
% 0.53/0.72          | ((k4_subset_1 @ X66 @ X65 @ X67) = (k2_xboole_0 @ X65 @ X67)))),
% 0.53/0.72      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.53/0.72  thf('115', plain,
% 0.53/0.72      (![X54 : $i, X55 : $i]:
% 0.53/0.72         ((k3_tarski @ (k2_tarski @ X54 @ X55)) = (k2_xboole_0 @ X54 @ X55))),
% 0.53/0.72      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.53/0.72  thf('116', plain,
% 0.53/0.72      (![X65 : $i, X66 : $i, X67 : $i]:
% 0.53/0.72         (~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ X66))
% 0.53/0.72          | ~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ X66))
% 0.53/0.72          | ((k4_subset_1 @ X66 @ X65 @ X67)
% 0.53/0.72              = (k3_tarski @ (k2_tarski @ X65 @ X67))))),
% 0.53/0.72      inference('demod', [status(thm)], ['114', '115'])).
% 0.53/0.72  thf('117', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (((k4_subset_1 @ sk_A @ sk_B @ X0)
% 0.53/0.72            = (k3_tarski @ (k2_tarski @ sk_B @ X0)))
% 0.53/0.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.53/0.72      inference('sup-', [status(thm)], ['113', '116'])).
% 0.53/0.72  thf('118', plain,
% 0.53/0.72      (((k4_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.53/0.72         = (k3_tarski @ (k2_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))))),
% 0.53/0.72      inference('sup-', [status(thm)], ['112', '117'])).
% 0.53/0.72  thf('119', plain,
% 0.53/0.72      (((k3_tarski @ (k2_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))
% 0.53/0.72         != (sk_A))),
% 0.53/0.72      inference('demod', [status(thm)], ['107', '118'])).
% 0.53/0.72  thf('120', plain, ($false),
% 0.53/0.72      inference('simplify_reflect-', [status(thm)], ['100', '119'])).
% 0.53/0.72  
% 0.53/0.72  % SZS output end Refutation
% 0.53/0.72  
% 0.53/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
