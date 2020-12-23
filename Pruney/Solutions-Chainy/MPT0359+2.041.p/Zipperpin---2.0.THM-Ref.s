%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AKXe8tbvNP

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 278 expanded)
%              Number of leaves         :   22 (  87 expanded)
%              Depth                    :   14
%              Number of atoms          :  640 (2136 expanded)
%              Number of equality atoms :   59 ( 186 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(t39_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
      <=> ( B
          = ( k2_subset_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
        <=> ( B
            = ( k2_subset_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('1',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_subset_1 @ X23 @ ( k3_subset_1 @ X23 @ X22 ) )
        = X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ( r2_hidden @ X10 @ X12 )
      | ( X12
       != ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('8',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('10',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ( m1_subset_1 @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('12',plain,(
    ! [X21: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['2','5','15'])).

thf('17',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['2','5','15'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('18',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('19',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_B )
    | ( ( k4_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('23',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['24'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('27',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ( m1_subset_1 @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X21: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['26'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('37',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','38'])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('40',plain,(
    ! [X18: $i] :
      ( ( k2_subset_1 @ X18 )
      = X18 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('41',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['20'])).

thf('42',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['24'])).

thf('44',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('46',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_A ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('49',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','50'])).

thf('52',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['20'])).

thf('53',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sat_resolution*',[status(thm)],['25','51','52'])).

thf('54',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_B ),
    inference(simpl_trail,[status(thm)],['23','53'])).

thf('55',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['19','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('57',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_subset_1 @ X23 @ ( k3_subset_1 @ X23 @ X22 ) )
        = X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('62',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('63',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ( m1_subset_1 @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X21: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['60','69'])).

thf('71',plain,(
    sk_A = sk_B ),
    inference(demod,[status(thm)],['16','55','70'])).

thf('72',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['24'])).

thf('73',plain,(
    ! [X18: $i] :
      ( ( k2_subset_1 @ X18 )
      = X18 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('74',plain,
    ( ( sk_B != sk_A )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    sk_B
 != ( k2_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['25','51'])).

thf('76',plain,(
    sk_B != sk_A ),
    inference(simpl_trail,[status(thm)],['74','75'])).

thf('77',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['71','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AKXe8tbvNP
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:25:54 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 196 iterations in 0.075s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.53  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.53  thf(t39_subset_1, conjecture,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53       ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.20/0.53         ( ( B ) = ( k2_subset_1 @ A ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i]:
% 0.20/0.53        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53          ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.20/0.53            ( ( B ) = ( k2_subset_1 @ A ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t39_subset_1])).
% 0.20/0.53  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(involutiveness_k3_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (![X22 : $i, X23 : $i]:
% 0.20/0.53         (((k3_subset_1 @ X23 @ (k3_subset_1 @ X23 @ X22)) = (X22))
% 0.20/0.53          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 0.20/0.53      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.53  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(d5_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (![X19 : $i, X20 : $i]:
% 0.20/0.53         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 0.20/0.53          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.53  thf(t36_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 0.20/0.53      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.20/0.53  thf(d1_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.20/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.53         (~ (r1_tarski @ X10 @ X11)
% 0.20/0.53          | (r2_hidden @ X10 @ X12)
% 0.20/0.53          | ((X12) != (k1_zfmisc_1 @ X11)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X10 : $i, X11 : $i]:
% 0.20/0.53         ((r2_hidden @ X10 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X10 @ X11))),
% 0.20/0.53      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (r2_hidden @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['6', '8'])).
% 0.20/0.53  thf(d2_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( v1_xboole_0 @ A ) =>
% 0.20/0.53         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.20/0.53       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.53         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (![X15 : $i, X16 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X15 @ X16)
% 0.20/0.53          | (m1_subset_1 @ X15 @ X16)
% 0.20/0.53          | (v1_xboole_0 @ X16))),
% 0.20/0.53      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.20/0.53          | (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.53  thf(fc1_subset_1, axiom,
% 0.20/0.53    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.53  thf('12', plain, (![X21 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X21))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.20/0.53      inference('clc', [status(thm)], ['11', '12'])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (![X19 : $i, X20 : $i]:
% 0.20/0.53         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 0.20/0.53          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.20/0.53           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['2', '5', '15'])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['2', '5', '15'])).
% 0.20/0.53  thf(t38_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.20/0.53       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (![X8 : $i, X9 : $i]:
% 0.20/0.53         (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X8)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      ((~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B)
% 0.20/0.53        | ((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      ((((sk_B) = (k2_subset_1 @ sk_A))
% 0.20/0.53        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.20/0.53         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.53      inference('split', [status(esa)], ['20'])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      (((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B))
% 0.20/0.53         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      ((((sk_B) != (k2_subset_1 @ sk_A))
% 0.20/0.53        | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (~ (((sk_B) = (k2_subset_1 @ sk_A))) | 
% 0.20/0.53       ~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.53      inference('split', [status(esa)], ['24'])).
% 0.20/0.53  thf(d10_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.53  thf('27', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.53      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (![X10 : $i, X11 : $i]:
% 0.20/0.53         ((r2_hidden @ X10 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X10 @ X11))),
% 0.20/0.53      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.53  thf('29', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (![X15 : $i, X16 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X15 @ X16)
% 0.20/0.53          | (m1_subset_1 @ X15 @ X16)
% 0.20/0.53          | (v1_xboole_0 @ X16))),
% 0.20/0.53      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.20/0.53          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.53  thf('32', plain, (![X21 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X21))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.53  thf('33', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.53      inference('clc', [status(thm)], ['31', '32'])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (![X19 : $i, X20 : $i]:
% 0.20/0.53         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 0.20/0.53          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.53  thf('36', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.53      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.53  thf(l32_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (![X3 : $i, X5 : $i]:
% 0.20/0.53         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.20/0.53      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.53  thf('38', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.53  thf('39', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['35', '38'])).
% 0.20/0.53  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.53  thf('40', plain, (![X18 : $i]: ((k2_subset_1 @ X18) = (X18))),
% 0.20/0.53      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      ((((sk_B) = (k2_subset_1 @ sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.53      inference('split', [status(esa)], ['20'])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['40', '41'])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.20/0.53         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.53      inference('split', [status(esa)], ['24'])).
% 0.20/0.53  thf('44', plain,
% 0.20/0.53      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A))
% 0.20/0.53         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.20/0.53             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['40', '41'])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_A) @ sk_A))
% 0.20/0.53         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.20/0.53             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.53      inference('demod', [status(thm)], ['44', '45'])).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      ((~ (r1_tarski @ k1_xboole_0 @ sk_A))
% 0.20/0.53         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.20/0.53             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['39', '46'])).
% 0.20/0.53  thf('48', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.53  thf('49', plain,
% 0.20/0.53      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 0.20/0.53      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.20/0.53  thf('50', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.53      inference('sup+', [status(thm)], ['48', '49'])).
% 0.20/0.53  thf('51', plain,
% 0.20/0.53      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.20/0.53       ~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['47', '50'])).
% 0.20/0.53  thf('52', plain,
% 0.20/0.53      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.20/0.53       (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.20/0.53      inference('split', [status(esa)], ['20'])).
% 0.20/0.53  thf('53', plain, (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['25', '51', '52'])).
% 0.20/0.53  thf('54', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B)),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['23', '53'])).
% 0.20/0.53  thf('55', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['19', '54'])).
% 0.20/0.53  thf('56', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.53      inference('clc', [status(thm)], ['31', '32'])).
% 0.20/0.53  thf('57', plain,
% 0.20/0.53      (![X22 : $i, X23 : $i]:
% 0.20/0.53         (((k3_subset_1 @ X23 @ (k3_subset_1 @ X23 @ X22)) = (X22))
% 0.20/0.53          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 0.20/0.53      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.20/0.53  thf('58', plain,
% 0.20/0.53      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['56', '57'])).
% 0.20/0.53  thf('59', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['35', '38'])).
% 0.20/0.53  thf('60', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['58', '59'])).
% 0.20/0.53  thf('61', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.53      inference('sup+', [status(thm)], ['48', '49'])).
% 0.20/0.53  thf('62', plain,
% 0.20/0.53      (![X10 : $i, X11 : $i]:
% 0.20/0.53         ((r2_hidden @ X10 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X10 @ X11))),
% 0.20/0.53      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.53  thf('63', plain,
% 0.20/0.53      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['61', '62'])).
% 0.20/0.53  thf('64', plain,
% 0.20/0.53      (![X15 : $i, X16 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X15 @ X16)
% 0.20/0.53          | (m1_subset_1 @ X15 @ X16)
% 0.20/0.53          | (v1_xboole_0 @ X16))),
% 0.20/0.53      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.53  thf('65', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.20/0.53          | (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.53  thf('66', plain, (![X21 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X21))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.53  thf('67', plain,
% 0.20/0.53      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.53      inference('clc', [status(thm)], ['65', '66'])).
% 0.20/0.53  thf('68', plain,
% 0.20/0.53      (![X19 : $i, X20 : $i]:
% 0.20/0.53         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 0.20/0.53          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.53  thf('69', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['67', '68'])).
% 0.20/0.53  thf('70', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['60', '69'])).
% 0.20/0.53  thf('71', plain, (((sk_A) = (sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['16', '55', '70'])).
% 0.20/0.53  thf('72', plain,
% 0.20/0.53      ((((sk_B) != (k2_subset_1 @ sk_A)))
% 0.20/0.53         <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.53      inference('split', [status(esa)], ['24'])).
% 0.20/0.53  thf('73', plain, (![X18 : $i]: ((k2_subset_1 @ X18) = (X18))),
% 0.20/0.53      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.53  thf('74', plain,
% 0.20/0.53      ((((sk_B) != (sk_A))) <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.53      inference('demod', [status(thm)], ['72', '73'])).
% 0.20/0.53  thf('75', plain, (~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['25', '51'])).
% 0.20/0.53  thf('76', plain, (((sk_B) != (sk_A))),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['74', '75'])).
% 0.20/0.53  thf('77', plain, ($false),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['71', '76'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
