%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9Ubr2oGMKC

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:40 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 173 expanded)
%              Number of leaves         :   25 (  59 expanded)
%              Depth                    :   12
%              Number of atoms          :  533 (1362 expanded)
%              Number of equality atoms :   58 ( 147 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_subset_1 @ X19 @ ( k3_subset_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_subset_1 @ X16 @ X17 )
        = ( k4_xboole_0 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['2','5'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('7',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('8',plain,
    ( ( sk_B_1
      = ( k2_subset_1 @ sk_A ) )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['8'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( ( k3_subset_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) @ sk_B_1 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('14',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( ( k3_subset_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
      | ( ( k3_subset_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('18',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('19',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('20',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('21',plain,
    ( ( ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf('22',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( sk_B_1
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( sk_B_1
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['23'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('25',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('26',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_subset_1 @ X19 @ ( k3_subset_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('28',plain,(
    ! [X14: $i] :
      ( ( k1_subset_1 @ X14 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('29',plain,(
    ! [X20: $i] :
      ( ( k2_subset_1 @ X20 )
      = ( k3_subset_1 @ X20 @ ( k1_subset_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('30',plain,(
    ! [X15: $i] :
      ( ( k2_subset_1 @ X15 )
      = X15 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('31',plain,(
    ! [X20: $i] :
      ( X20
      = ( k3_subset_1 @ X20 @ ( k1_subset_1 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X15: $i] :
      ( ( k2_subset_1 @ X15 )
      = X15 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('35',plain,
    ( ( sk_B_1
      = ( k2_subset_1 @ sk_A ) )
   <= ( sk_B_1
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['8'])).

thf('36',plain,
    ( ( sk_B_1 = sk_A )
   <= ( sk_B_1
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['23'])).

thf('38',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
      & ( sk_B_1
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_B_1 = sk_A )
   <= ( sk_B_1
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('40',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_A ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
      & ( sk_B_1
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
      & ( sk_B_1
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','40'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('42',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('43',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
    | ( sk_B_1
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
    | ( sk_B_1
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['8'])).

thf('45',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['24','43','44'])).

thf('46',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['22','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('48',plain,(
    sk_A = sk_B_1 ),
    inference(demod,[status(thm)],['6','46','47'])).

thf('49',plain,
    ( ( sk_B_1
     != ( k2_subset_1 @ sk_A ) )
   <= ( sk_B_1
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['23'])).

thf('50',plain,(
    ! [X15: $i] :
      ( ( k2_subset_1 @ X15 )
      = X15 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('51',plain,
    ( ( sk_B_1 != sk_A )
   <= ( sk_B_1
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    sk_B_1
 != ( k2_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['24','43'])).

thf('53',plain,(
    sk_B_1 != sk_A ),
    inference(simpl_trail,[status(thm)],['51','52'])).

thf('54',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['48','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9Ubr2oGMKC
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:50:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 190 iterations in 0.051s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.51  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.20/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.51  thf(t39_subset_1, conjecture,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.51       ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.20/0.51         ( ( B ) = ( k2_subset_1 @ A ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i]:
% 0.20/0.51        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.51          ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.20/0.51            ( ( B ) = ( k2_subset_1 @ A ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t39_subset_1])).
% 0.20/0.51  thf('0', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(involutiveness_k3_subset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.51       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (![X18 : $i, X19 : $i]:
% 0.20/0.51         (((k3_subset_1 @ X19 @ (k3_subset_1 @ X19 @ X18)) = (X18))
% 0.20/0.51          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.20/0.51      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.51  thf('3', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(d5_subset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.51       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X16 : $i, X17 : $i]:
% 0.20/0.51         (((k3_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))
% 0.20/0.51          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.20/0.51      inference('demod', [status(thm)], ['2', '5'])).
% 0.20/0.51  thf(t7_xboole_0, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.51          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.20/0.51      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      ((((sk_B_1) = (k2_subset_1 @ sk_A))
% 0.20/0.51        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1))
% 0.20/0.51         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)))),
% 0.20/0.51      inference('split', [status(esa)], ['8'])).
% 0.20/0.51  thf(d3_tarski, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.51          | (r2_hidden @ X0 @ X2)
% 0.20/0.51          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          ((r2_hidden @ X0 @ sk_B_1)
% 0.20/0.51           | ~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B_1))))
% 0.20/0.51         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (((((k3_subset_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.20/0.51         | (r2_hidden @ (sk_B @ (k3_subset_1 @ sk_A @ sk_B_1)) @ sk_B_1)))
% 0.20/0.51         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['7', '11'])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.20/0.51      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.51  thf(t3_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.51            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.51       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.51            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X6 @ X4)
% 0.20/0.51          | ~ (r2_hidden @ X6 @ X7)
% 0.20/0.51          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((X0) = (k1_xboole_0))
% 0.20/0.51          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.20/0.51          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (((((k3_subset_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.20/0.51         | ~ (r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)
% 0.20/0.51         | ((k3_subset_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))
% 0.20/0.51         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['12', '15'])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.51  thf(t79_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X13)),
% 0.20/0.51      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (((((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.20/0.51         | ((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))))
% 0.20/0.51         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)))),
% 0.20/0.51      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      ((((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.20/0.51         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      ((((sk_B_1) != (k2_subset_1 @ sk_A))
% 0.20/0.51        | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      (~ (((sk_B_1) = (k2_subset_1 @ sk_A))) | 
% 0.20/0.51       ~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 0.20/0.51      inference('split', [status(esa)], ['23'])).
% 0.20/0.51  thf(t4_subset_1, axiom,
% 0.20/0.51    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (![X21 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X21))),
% 0.20/0.51      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      (![X18 : $i, X19 : $i]:
% 0.20/0.51         (((k3_subset_1 @ X19 @ (k3_subset_1 @ X19 @ X18)) = (X18))
% 0.20/0.51          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.20/0.51      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.51  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.51  thf('28', plain, (![X14 : $i]: ((k1_subset_1 @ X14) = (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.20/0.51  thf(t22_subset_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      (![X20 : $i]:
% 0.20/0.51         ((k2_subset_1 @ X20) = (k3_subset_1 @ X20 @ (k1_subset_1 @ X20)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.20/0.51  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.51  thf('30', plain, (![X15 : $i]: ((k2_subset_1 @ X15) = (X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      (![X20 : $i]: ((X20) = (k3_subset_1 @ X20 @ (k1_subset_1 @ X20)))),
% 0.20/0.51      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.51  thf('32', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.20/0.51      inference('sup+', [status(thm)], ['28', '31'])).
% 0.20/0.51  thf('33', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.51      inference('demod', [status(thm)], ['27', '32'])).
% 0.20/0.51  thf('34', plain, (![X15 : $i]: ((k2_subset_1 @ X15) = (X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      ((((sk_B_1) = (k2_subset_1 @ sk_A)))
% 0.20/0.51         <= ((((sk_B_1) = (k2_subset_1 @ sk_A))))),
% 0.20/0.51      inference('split', [status(esa)], ['8'])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      ((((sk_B_1) = (sk_A))) <= ((((sk_B_1) = (k2_subset_1 @ sk_A))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['34', '35'])).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1))
% 0.20/0.51         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)))),
% 0.20/0.51      inference('split', [status(esa)], ['23'])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_A))
% 0.20/0.51         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)) & 
% 0.20/0.51             (((sk_B_1) = (k2_subset_1 @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      ((((sk_B_1) = (sk_A))) <= ((((sk_B_1) = (k2_subset_1 @ sk_A))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['34', '35'])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_A) @ sk_A))
% 0.20/0.51         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)) & 
% 0.20/0.51             (((sk_B_1) = (k2_subset_1 @ sk_A))))),
% 0.20/0.51      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.51  thf('41', plain,
% 0.20/0.51      ((~ (r1_tarski @ k1_xboole_0 @ sk_A))
% 0.20/0.51         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)) & 
% 0.20/0.51             (((sk_B_1) = (k2_subset_1 @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['33', '40'])).
% 0.20/0.51  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.51  thf('42', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 0.20/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)) | 
% 0.20/0.51       ~ (((sk_B_1) = (k2_subset_1 @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['41', '42'])).
% 0.20/0.51  thf('44', plain,
% 0.20/0.51      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)) | 
% 0.20/0.51       (((sk_B_1) = (k2_subset_1 @ sk_A)))),
% 0.20/0.51      inference('split', [status(esa)], ['8'])).
% 0.20/0.51  thf('45', plain, (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['24', '43', '44'])).
% 0.20/0.51  thf('46', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['22', '45'])).
% 0.20/0.51  thf('47', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.20/0.51      inference('sup+', [status(thm)], ['28', '31'])).
% 0.20/0.51  thf('48', plain, (((sk_A) = (sk_B_1))),
% 0.20/0.51      inference('demod', [status(thm)], ['6', '46', '47'])).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      ((((sk_B_1) != (k2_subset_1 @ sk_A)))
% 0.20/0.51         <= (~ (((sk_B_1) = (k2_subset_1 @ sk_A))))),
% 0.20/0.51      inference('split', [status(esa)], ['23'])).
% 0.20/0.51  thf('50', plain, (![X15 : $i]: ((k2_subset_1 @ X15) = (X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.51  thf('51', plain,
% 0.20/0.51      ((((sk_B_1) != (sk_A))) <= (~ (((sk_B_1) = (k2_subset_1 @ sk_A))))),
% 0.20/0.51      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.51  thf('52', plain, (~ (((sk_B_1) = (k2_subset_1 @ sk_A)))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['24', '43'])).
% 0.20/0.51  thf('53', plain, (((sk_B_1) != (sk_A))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['51', '52'])).
% 0.20/0.51  thf('54', plain, ($false),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['48', '53'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
