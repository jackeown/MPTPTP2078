%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aQqckc72Yb

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:34 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 223 expanded)
%              Number of leaves         :   25 (  72 expanded)
%              Depth                    :   17
%              Number of atoms          :  614 (1705 expanded)
%              Number of equality atoms :   68 ( 172 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ X20 )
      | ( r2_hidden @ X19 @ X20 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X25: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X25 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X17 @ X16 )
      | ( r1_tarski @ X17 @ X15 )
      | ( X16
       != ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('6',plain,(
    ! [X15: $i,X17: $i] :
      ( ( r1_tarski @ X17 @ X15 )
      | ~ ( r2_hidden @ X17 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['4','6'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('9',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('11',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('14',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_subset_1 @ X23 @ X24 )
        = ( k4_xboole_0 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('17',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('19',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ( ( k4_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('24',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['26'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ( r2_hidden @ X14 @ X16 )
      | ( X16
       != ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('31',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ( m1_subset_1 @ X19 @ X20 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X25: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_subset_1 @ X23 @ X24 )
        = ( k4_xboole_0 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('40',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('43',plain,(
    ! [X22: $i] :
      ( ( k2_subset_1 @ X22 )
      = X22 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('44',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['24'])).

thf('45',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['26'])).

thf('47',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('49',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_A ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','49'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('51',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('52',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','54'])).

thf('56',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['24'])).

thf('57',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sat_resolution*',[status(thm)],['27','55','56'])).

thf('58',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(simpl_trail,[status(thm)],['25','57'])).

thf('59',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('60',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['22','23','58','59'])).

thf('61',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['17','60'])).

thf('62',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('63',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('65',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    sk_A = sk_B ),
    inference('sup+',[status(thm)],['14','65'])).

thf('67',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['26'])).

thf('68',plain,(
    ! [X22: $i] :
      ( ( k2_subset_1 @ X22 )
      = X22 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('69',plain,
    ( ( sk_B != sk_A )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    sk_B
 != ( k2_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['27','55'])).

thf('71',plain,(
    sk_B != sk_A ),
    inference(simpl_trail,[status(thm)],['69','70'])).

thf('72',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['66','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aQqckc72Yb
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:57:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 293 iterations in 0.095s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.54  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.54  thf(t39_subset_1, conjecture,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.54       ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.20/0.54         ( ( B ) = ( k2_subset_1 @ A ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i,B:$i]:
% 0.20/0.54        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.54          ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.20/0.54            ( ( B ) = ( k2_subset_1 @ A ) ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t39_subset_1])).
% 0.20/0.54  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(d2_subset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( v1_xboole_0 @ A ) =>
% 0.20/0.54         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.20/0.54       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.54         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      (![X19 : $i, X20 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X19 @ X20)
% 0.20/0.54          | (r2_hidden @ X19 @ X20)
% 0.20/0.54          | (v1_xboole_0 @ X20))),
% 0.20/0.54      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.54        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.54  thf(fc1_subset_1, axiom,
% 0.20/0.54    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.54  thf('3', plain, (![X25 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X25))),
% 0.20/0.54      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.54  thf('4', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.54      inference('clc', [status(thm)], ['2', '3'])).
% 0.20/0.54  thf(d1_zfmisc_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.20/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X17 @ X16)
% 0.20/0.54          | (r1_tarski @ X17 @ X15)
% 0.20/0.54          | ((X16) != (k1_zfmisc_1 @ X15)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      (![X15 : $i, X17 : $i]:
% 0.20/0.54         ((r1_tarski @ X17 @ X15) | ~ (r2_hidden @ X17 @ (k1_zfmisc_1 @ X15)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.54  thf('7', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.20/0.54      inference('sup-', [status(thm)], ['4', '6'])).
% 0.20/0.54  thf(l32_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      (![X5 : $i, X7 : $i]:
% 0.20/0.54         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.20/0.54      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.54  thf('9', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.54  thf(t48_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.54  thf('10', plain,
% 0.20/0.54      (![X11 : $i, X12 : $i]:
% 0.20/0.54         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.20/0.54           = (k3_xboole_0 @ X11 @ X12))),
% 0.20/0.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      (((k4_xboole_0 @ sk_B @ k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.20/0.54      inference('sup+', [status(thm)], ['9', '10'])).
% 0.20/0.54  thf(t3_boole, axiom,
% 0.20/0.54    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.54  thf('12', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.20/0.54      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.54  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.54  thf('14', plain, (((sk_B) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.20/0.54  thf('15', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(d5_subset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.54       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      (![X23 : $i, X24 : $i]:
% 0.20/0.54         (((k3_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))
% 0.20/0.54          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.54  thf('18', plain,
% 0.20/0.54      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      (![X11 : $i, X12 : $i]:
% 0.20/0.54         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.20/0.54           = (k3_xboole_0 @ X11 @ X12))),
% 0.20/0.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.54  thf(t38_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.20/0.54       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.54  thf('20', plain,
% 0.20/0.54      (![X8 : $i, X9 : $i]:
% 0.20/0.54         (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X8)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.20/0.54          | ((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.54  thf('22', plain,
% 0.20/0.54      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.20/0.54           (k3_xboole_0 @ sk_A @ sk_B))
% 0.20/0.54        | ((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['18', '21'])).
% 0.20/0.54  thf('23', plain, (((sk_B) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.20/0.54  thf('24', plain,
% 0.20/0.54      ((((sk_B) = (k2_subset_1 @ sk_A))
% 0.20/0.54        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('25', plain,
% 0.20/0.54      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.20/0.54         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.54      inference('split', [status(esa)], ['24'])).
% 0.20/0.54  thf('26', plain,
% 0.20/0.54      ((((sk_B) != (k2_subset_1 @ sk_A))
% 0.20/0.54        | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('27', plain,
% 0.20/0.54      (~ (((sk_B) = (k2_subset_1 @ sk_A))) | 
% 0.20/0.54       ~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.54      inference('split', [status(esa)], ['26'])).
% 0.20/0.54  thf(d10_xboole_0, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.54  thf('28', plain,
% 0.20/0.54      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.54  thf('29', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.20/0.54      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.54  thf('30', plain,
% 0.20/0.54      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.54         (~ (r1_tarski @ X14 @ X15)
% 0.20/0.54          | (r2_hidden @ X14 @ X16)
% 0.20/0.54          | ((X16) != (k1_zfmisc_1 @ X15)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.54  thf('31', plain,
% 0.20/0.54      (![X14 : $i, X15 : $i]:
% 0.20/0.54         ((r2_hidden @ X14 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X14 @ X15))),
% 0.20/0.54      inference('simplify', [status(thm)], ['30'])).
% 0.20/0.54  thf('32', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['29', '31'])).
% 0.20/0.54  thf('33', plain,
% 0.20/0.54      (![X19 : $i, X20 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X19 @ X20)
% 0.20/0.54          | (m1_subset_1 @ X19 @ X20)
% 0.20/0.54          | (v1_xboole_0 @ X20))),
% 0.20/0.54      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.54  thf('34', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.20/0.55          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.55  thf('35', plain, (![X25 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X25))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.55  thf('36', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.55      inference('clc', [status(thm)], ['34', '35'])).
% 0.20/0.55  thf('37', plain,
% 0.20/0.55      (![X23 : $i, X24 : $i]:
% 0.20/0.55         (((k3_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))
% 0.20/0.55          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23)))),
% 0.20/0.55      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.55  thf('38', plain,
% 0.20/0.55      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.55  thf('39', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.20/0.55      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.55  thf('40', plain,
% 0.20/0.55      (![X5 : $i, X7 : $i]:
% 0.20/0.55         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.20/0.55      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.55  thf('41', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.55  thf('42', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['38', '41'])).
% 0.20/0.55  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.55  thf('43', plain, (![X22 : $i]: ((k2_subset_1 @ X22) = (X22))),
% 0.20/0.55      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.55  thf('44', plain,
% 0.20/0.55      ((((sk_B) = (k2_subset_1 @ sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.55      inference('split', [status(esa)], ['24'])).
% 0.20/0.55  thf('45', plain,
% 0.20/0.55      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.55      inference('sup+', [status(thm)], ['43', '44'])).
% 0.20/0.55  thf('46', plain,
% 0.20/0.55      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.20/0.55         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.55      inference('split', [status(esa)], ['26'])).
% 0.20/0.55  thf('47', plain,
% 0.20/0.55      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A))
% 0.20/0.55         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.20/0.55             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.55  thf('48', plain,
% 0.20/0.55      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.55      inference('sup+', [status(thm)], ['43', '44'])).
% 0.20/0.55  thf('49', plain,
% 0.20/0.55      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_A) @ sk_A))
% 0.20/0.55         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.20/0.55             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.55      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.55  thf('50', plain,
% 0.20/0.55      ((~ (r1_tarski @ k1_xboole_0 @ sk_A))
% 0.20/0.55         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.20/0.55             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['42', '49'])).
% 0.20/0.55  thf(t4_boole, axiom,
% 0.20/0.55    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.55  thf('51', plain,
% 0.20/0.55      (![X13 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X13) = (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [t4_boole])).
% 0.20/0.55  thf('52', plain,
% 0.20/0.55      (![X5 : $i, X6 : $i]:
% 0.20/0.55         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 0.20/0.55      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.55  thf('53', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.55  thf('54', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.55      inference('simplify', [status(thm)], ['53'])).
% 0.20/0.55  thf('55', plain,
% 0.20/0.55      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.20/0.55       ~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.20/0.55      inference('demod', [status(thm)], ['50', '54'])).
% 0.20/0.55  thf('56', plain,
% 0.20/0.55      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.20/0.55       (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.20/0.55      inference('split', [status(esa)], ['24'])).
% 0.20/0.55  thf('57', plain, (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.55      inference('sat_resolution*', [status(thm)], ['27', '55', '56'])).
% 0.20/0.55  thf('58', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)),
% 0.20/0.55      inference('simpl_trail', [status(thm)], ['25', '57'])).
% 0.20/0.55  thf('59', plain,
% 0.20/0.55      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.55  thf('60', plain, (((k3_subset_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.55      inference('demod', [status(thm)], ['22', '23', '58', '59'])).
% 0.20/0.55  thf('61', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.55      inference('demod', [status(thm)], ['17', '60'])).
% 0.20/0.55  thf('62', plain,
% 0.20/0.55      (![X11 : $i, X12 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.20/0.55           = (k3_xboole_0 @ X11 @ X12))),
% 0.20/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.55  thf('63', plain,
% 0.20/0.55      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.55      inference('sup+', [status(thm)], ['61', '62'])).
% 0.20/0.55  thf('64', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.20/0.55      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.55  thf('65', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.55      inference('demod', [status(thm)], ['63', '64'])).
% 0.20/0.55  thf('66', plain, (((sk_A) = (sk_B))),
% 0.20/0.55      inference('sup+', [status(thm)], ['14', '65'])).
% 0.20/0.55  thf('67', plain,
% 0.20/0.55      ((((sk_B) != (k2_subset_1 @ sk_A)))
% 0.20/0.55         <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.55      inference('split', [status(esa)], ['26'])).
% 0.20/0.55  thf('68', plain, (![X22 : $i]: ((k2_subset_1 @ X22) = (X22))),
% 0.20/0.55      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.55  thf('69', plain,
% 0.20/0.55      ((((sk_B) != (sk_A))) <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.55      inference('demod', [status(thm)], ['67', '68'])).
% 0.20/0.55  thf('70', plain, (~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.20/0.55      inference('sat_resolution*', [status(thm)], ['27', '55'])).
% 0.20/0.55  thf('71', plain, (((sk_B) != (sk_A))),
% 0.20/0.55      inference('simpl_trail', [status(thm)], ['69', '70'])).
% 0.20/0.55  thf('72', plain, ($false),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)], ['66', '71'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
