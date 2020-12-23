%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5ebLBtXnwZ

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:52 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 145 expanded)
%              Number of leaves         :   34 (  57 expanded)
%              Depth                    :   13
%              Number of atoms          :  652 (1061 expanded)
%              Number of equality atoms :   67 ( 106 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X47: $i,X48: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X47 @ X48 ) @ ( k1_zfmisc_1 @ X47 ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('2',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X51 ) )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ X51 ) )
      | ( ( k4_subset_1 @ X51 @ X50 @ X52 )
        = ( k2_xboole_0 @ X50 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k3_subset_1 @ X45 @ X46 )
        = ( k4_xboole_0 @ X45 @ X46 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('9',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['9','14'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('20',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['17','18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('24',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    = ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['22','27'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('30',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('32',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('33',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
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

thf('36',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ X42 )
      | ( r2_hidden @ X41 @ X42 )
      | ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('38',plain,(
    ! [X49: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('39',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['37','38'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('40',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X37 @ X36 )
      | ( r1_tarski @ X37 @ X35 )
      | ( X36
       != ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('41',plain,(
    ! [X35: $i,X37: $i] :
      ( ( r1_tarski @ X37 @ X35 )
      | ~ ( r2_hidden @ X37 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['39','41'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('43',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('44',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('46',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('49',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('50',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('51',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('52',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('53',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( sk_A
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['51','56'])).

thf('58',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('59',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','59'])).

thf('61',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['6','60'])).

thf('62',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('63',plain,(
    ! [X44: $i] :
      ( ( k2_subset_1 @ X44 )
      = X44 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('64',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['61','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5ebLBtXnwZ
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:32:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.53  % Solved by: fo/fo7.sh
% 0.19/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.53  % done 297 iterations in 0.081s
% 0.19/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.53  % SZS output start Refutation
% 0.19/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.19/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.53  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.19/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.53  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.19/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.53  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.19/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.53  thf(t25_subset_1, conjecture,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.53       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.19/0.53         ( k2_subset_1 @ A ) ) ))).
% 0.19/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.53    (~( ![A:$i,B:$i]:
% 0.19/0.53        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.53          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.19/0.53            ( k2_subset_1 @ A ) ) ) )),
% 0.19/0.53    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 0.19/0.53  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(dt_k3_subset_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.53       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.53  thf('1', plain,
% 0.19/0.53      (![X47 : $i, X48 : $i]:
% 0.19/0.53         ((m1_subset_1 @ (k3_subset_1 @ X47 @ X48) @ (k1_zfmisc_1 @ X47))
% 0.19/0.53          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X47)))),
% 0.19/0.53      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.19/0.53  thf('2', plain,
% 0.19/0.53      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.53  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(redefinition_k4_subset_1, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i]:
% 0.19/0.53     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.19/0.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.53       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.19/0.53  thf('4', plain,
% 0.19/0.53      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ X51))
% 0.19/0.53          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ X51))
% 0.19/0.53          | ((k4_subset_1 @ X51 @ X50 @ X52) = (k2_xboole_0 @ X50 @ X52)))),
% 0.19/0.53      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.19/0.53  thf('5', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.19/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.53  thf('6', plain,
% 0.19/0.53      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.19/0.53         = (k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['2', '5'])).
% 0.19/0.53  thf('7', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(d5_subset_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.53       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.19/0.53  thf('8', plain,
% 0.19/0.53      (![X45 : $i, X46 : $i]:
% 0.19/0.53         (((k3_subset_1 @ X45 @ X46) = (k4_xboole_0 @ X45 @ X46))
% 0.19/0.53          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X45)))),
% 0.19/0.53      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.19/0.53  thf('9', plain,
% 0.19/0.53      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.53  thf(t79_xboole_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.19/0.53  thf('10', plain,
% 0.19/0.53      (![X12 : $i, X13 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X13)),
% 0.19/0.53      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.19/0.53  thf(d7_xboole_0, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.19/0.53       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.53  thf('11', plain,
% 0.19/0.53      (![X4 : $i, X5 : $i]:
% 0.19/0.53         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.19/0.53      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.19/0.53  thf('12', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.19/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.53  thf(commutativity_k3_xboole_0, axiom,
% 0.19/0.53    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.19/0.53  thf('13', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.53  thf('14', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.19/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.19/0.53  thf('15', plain,
% 0.19/0.53      (((k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.19/0.53      inference('sup+', [status(thm)], ['9', '14'])).
% 0.19/0.53  thf(t100_xboole_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.53  thf('16', plain,
% 0.19/0.53      (![X7 : $i, X8 : $i]:
% 0.19/0.53         ((k4_xboole_0 @ X7 @ X8)
% 0.19/0.53           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.53  thf('17', plain,
% 0.19/0.53      (((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.19/0.53         = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.19/0.53      inference('sup+', [status(thm)], ['15', '16'])).
% 0.19/0.53  thf(commutativity_k5_xboole_0, axiom,
% 0.19/0.53    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.19/0.53  thf('18', plain,
% 0.19/0.53      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.19/0.53      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.19/0.53  thf('19', plain,
% 0.19/0.53      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.19/0.53      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.19/0.53  thf(t5_boole, axiom,
% 0.19/0.53    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.53  thf('20', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.19/0.53      inference('cnf', [status(esa)], [t5_boole])).
% 0.19/0.53  thf('21', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.19/0.53      inference('sup+', [status(thm)], ['19', '20'])).
% 0.19/0.53  thf('22', plain,
% 0.19/0.53      (((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.19/0.53      inference('demod', [status(thm)], ['17', '18', '21'])).
% 0.19/0.53  thf('23', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.19/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.19/0.53  thf('24', plain,
% 0.19/0.53      (![X7 : $i, X8 : $i]:
% 0.19/0.53         ((k4_xboole_0 @ X7 @ X8)
% 0.19/0.53           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.53  thf('25', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.19/0.53           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.19/0.53      inference('sup+', [status(thm)], ['23', '24'])).
% 0.19/0.53  thf('26', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.19/0.53      inference('cnf', [status(esa)], [t5_boole])).
% 0.19/0.53  thf('27', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.19/0.53      inference('demod', [status(thm)], ['25', '26'])).
% 0.19/0.53  thf('28', plain,
% 0.19/0.53      (((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)
% 0.19/0.53         = (k3_subset_1 @ sk_A @ sk_B))),
% 0.19/0.53      inference('sup+', [status(thm)], ['22', '27'])).
% 0.19/0.53  thf(t98_xboole_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.19/0.53  thf('29', plain,
% 0.19/0.53      (![X18 : $i, X19 : $i]:
% 0.19/0.53         ((k2_xboole_0 @ X18 @ X19)
% 0.19/0.53           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.19/0.53  thf('30', plain,
% 0.19/0.53      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.19/0.53         = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.19/0.53      inference('sup+', [status(thm)], ['28', '29'])).
% 0.19/0.53  thf('31', plain,
% 0.19/0.53      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.53  thf('32', plain,
% 0.19/0.53      (![X18 : $i, X19 : $i]:
% 0.19/0.53         ((k2_xboole_0 @ X18 @ X19)
% 0.19/0.53           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.19/0.53  thf('33', plain,
% 0.19/0.53      (((k2_xboole_0 @ sk_B @ sk_A)
% 0.19/0.53         = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.19/0.53      inference('sup+', [status(thm)], ['31', '32'])).
% 0.19/0.53  thf('34', plain,
% 0.19/0.53      (((k2_xboole_0 @ sk_B @ sk_A)
% 0.19/0.53         = (k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.19/0.53      inference('sup+', [status(thm)], ['30', '33'])).
% 0.19/0.53  thf('35', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(d2_subset_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( ( v1_xboole_0 @ A ) =>
% 0.19/0.53         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.19/0.53       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.53         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.19/0.53  thf('36', plain,
% 0.19/0.53      (![X41 : $i, X42 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ X41 @ X42)
% 0.19/0.53          | (r2_hidden @ X41 @ X42)
% 0.19/0.53          | (v1_xboole_0 @ X42))),
% 0.19/0.53      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.19/0.53  thf('37', plain,
% 0.19/0.53      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.19/0.53        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['35', '36'])).
% 0.19/0.53  thf(fc1_subset_1, axiom,
% 0.19/0.53    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.53  thf('38', plain, (![X49 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X49))),
% 0.19/0.53      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.19/0.53  thf('39', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.53      inference('clc', [status(thm)], ['37', '38'])).
% 0.19/0.53  thf(d1_zfmisc_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.19/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.19/0.53  thf('40', plain,
% 0.19/0.53      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.19/0.53         (~ (r2_hidden @ X37 @ X36)
% 0.19/0.53          | (r1_tarski @ X37 @ X35)
% 0.19/0.53          | ((X36) != (k1_zfmisc_1 @ X35)))),
% 0.19/0.53      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.19/0.53  thf('41', plain,
% 0.19/0.53      (![X35 : $i, X37 : $i]:
% 0.19/0.53         ((r1_tarski @ X37 @ X35) | ~ (r2_hidden @ X37 @ (k1_zfmisc_1 @ X35)))),
% 0.19/0.53      inference('simplify', [status(thm)], ['40'])).
% 0.19/0.53  thf('42', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.19/0.53      inference('sup-', [status(thm)], ['39', '41'])).
% 0.19/0.53  thf(t28_xboole_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.53  thf('43', plain,
% 0.19/0.53      (![X9 : $i, X10 : $i]:
% 0.19/0.53         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.19/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.53  thf('44', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.19/0.53      inference('sup-', [status(thm)], ['42', '43'])).
% 0.19/0.53  thf('45', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.53  thf('46', plain,
% 0.19/0.53      (![X7 : $i, X8 : $i]:
% 0.19/0.53         ((k4_xboole_0 @ X7 @ X8)
% 0.19/0.53           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.53  thf('47', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((k4_xboole_0 @ X0 @ X1)
% 0.19/0.53           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.19/0.53      inference('sup+', [status(thm)], ['45', '46'])).
% 0.19/0.53  thf('48', plain,
% 0.19/0.53      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.53      inference('sup+', [status(thm)], ['44', '47'])).
% 0.19/0.53  thf('49', plain,
% 0.19/0.53      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.53  thf('50', plain,
% 0.19/0.53      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.19/0.53      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.19/0.53  thf('51', plain,
% 0.19/0.53      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_B @ sk_A))),
% 0.19/0.53      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.19/0.53  thf(t92_xboole_1, axiom,
% 0.19/0.53    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.53  thf('52', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ X17) = (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.19/0.53  thf(t91_xboole_1, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i]:
% 0.19/0.53     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.19/0.53       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.19/0.53  thf('53', plain,
% 0.19/0.53      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.19/0.53         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 0.19/0.53           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.19/0.53  thf('54', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.19/0.53           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.19/0.53      inference('sup+', [status(thm)], ['52', '53'])).
% 0.19/0.53  thf('55', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.19/0.53      inference('sup+', [status(thm)], ['19', '20'])).
% 0.19/0.53  thf('56', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.19/0.53      inference('demod', [status(thm)], ['54', '55'])).
% 0.19/0.53  thf('57', plain,
% 0.19/0.53      (((sk_A) = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.19/0.53      inference('sup+', [status(thm)], ['51', '56'])).
% 0.19/0.53  thf('58', plain,
% 0.19/0.53      (((k2_xboole_0 @ sk_B @ sk_A)
% 0.19/0.53         = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.19/0.53      inference('sup+', [status(thm)], ['31', '32'])).
% 0.19/0.53  thf('59', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.19/0.53      inference('sup+', [status(thm)], ['57', '58'])).
% 0.19/0.53  thf('60', plain,
% 0.19/0.53      (((sk_A) = (k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.19/0.53      inference('demod', [status(thm)], ['34', '59'])).
% 0.19/0.53  thf('61', plain,
% 0.19/0.53      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_A))),
% 0.19/0.53      inference('demod', [status(thm)], ['6', '60'])).
% 0.19/0.53  thf('62', plain,
% 0.19/0.53      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.19/0.53         != (k2_subset_1 @ sk_A))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.19/0.53  thf('63', plain, (![X44 : $i]: ((k2_subset_1 @ X44) = (X44))),
% 0.19/0.53      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.19/0.53  thf('64', plain,
% 0.19/0.53      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.19/0.53      inference('demod', [status(thm)], ['62', '63'])).
% 0.19/0.53  thf('65', plain, ($false),
% 0.19/0.53      inference('simplify_reflect-', [status(thm)], ['61', '64'])).
% 0.19/0.53  
% 0.19/0.53  % SZS output end Refutation
% 0.19/0.53  
% 0.19/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
