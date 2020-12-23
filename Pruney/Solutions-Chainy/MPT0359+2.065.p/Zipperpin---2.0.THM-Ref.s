%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mH4TPFn5yj

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:40 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 178 expanded)
%              Number of leaves         :   27 (  61 expanded)
%              Depth                    :   12
%              Number of atoms          :  578 (1407 expanded)
%              Number of equality atoms :   63 ( 152 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ! [X22: $i,X23: $i] :
      ( ( ( k3_subset_1 @ X23 @ ( k3_subset_1 @ X23 @ X22 ) )
        = X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ( ( k3_subset_1 @ X20 @ X21 )
        = ( k4_xboole_0 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
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
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
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

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,
    ( ( ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
      = ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('12',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('13',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
        | ( r2_hidden @ X0 @ sk_B_1 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,
    ( ( ( ( k3_subset_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) @ sk_B_1 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
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

thf('17',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( ( k3_subset_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
      | ( ( k3_subset_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('21',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('22',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('23',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('24',plain,
    ( ( ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['19','20','21','22','23'])).

thf('25',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( sk_B_1
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( sk_B_1
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['26'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('28',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('29',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_subset_1 @ X23 @ ( k3_subset_1 @ X23 @ X22 ) )
        = X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('31',plain,(
    ! [X18: $i] :
      ( ( k1_subset_1 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('32',plain,(
    ! [X24: $i] :
      ( ( k2_subset_1 @ X24 )
      = ( k3_subset_1 @ X24 @ ( k1_subset_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('33',plain,(
    ! [X19: $i] :
      ( ( k2_subset_1 @ X19 )
      = X19 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('34',plain,(
    ! [X24: $i] :
      ( X24
      = ( k3_subset_1 @ X24 @ ( k1_subset_1 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','35'])).

thf('37',plain,(
    ! [X19: $i] :
      ( ( k2_subset_1 @ X19 )
      = X19 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('38',plain,
    ( ( sk_B_1
      = ( k2_subset_1 @ sk_A ) )
   <= ( sk_B_1
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['8'])).

thf('39',plain,
    ( ( sk_B_1 = sk_A )
   <= ( sk_B_1
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['26'])).

thf('41',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
      & ( sk_B_1
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( sk_B_1 = sk_A )
   <= ( sk_B_1
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('43',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_A ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
      & ( sk_B_1
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
      & ( sk_B_1
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','43'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('45',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ X15 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('46',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
    | ( sk_B_1
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
    | ( sk_B_1
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['8'])).

thf('48',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['27','46','47'])).

thf('49',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['25','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('51',plain,(
    sk_A = sk_B_1 ),
    inference(demod,[status(thm)],['6','49','50'])).

thf('52',plain,
    ( ( sk_B_1
     != ( k2_subset_1 @ sk_A ) )
   <= ( sk_B_1
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['26'])).

thf('53',plain,(
    ! [X19: $i] :
      ( ( k2_subset_1 @ X19 )
      = X19 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('54',plain,
    ( ( sk_B_1 != sk_A )
   <= ( sk_B_1
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    sk_B_1
 != ( k2_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['27','46'])).

thf('56',plain,(
    sk_B_1 != sk_A ),
    inference(simpl_trail,[status(thm)],['54','55'])).

thf('57',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['51','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mH4TPFn5yj
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:32:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 230 iterations in 0.086s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.52  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(t39_subset_1, conjecture,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.52       ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.20/0.52         ( ( B ) = ( k2_subset_1 @ A ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i]:
% 0.20/0.52        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.52          ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.20/0.52            ( ( B ) = ( k2_subset_1 @ A ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t39_subset_1])).
% 0.20/0.52  thf('0', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(involutiveness_k3_subset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.52       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (![X22 : $i, X23 : $i]:
% 0.20/0.52         (((k3_subset_1 @ X23 @ (k3_subset_1 @ X23 @ X22)) = (X22))
% 0.20/0.52          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 0.20/0.52      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.52  thf('3', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(d5_subset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.52       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (![X20 : $i, X21 : $i]:
% 0.20/0.52         (((k3_subset_1 @ X20 @ X21) = (k4_xboole_0 @ X20 @ X21))
% 0.20/0.52          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.20/0.52      inference('demod', [status(thm)], ['2', '5'])).
% 0.20/0.52  thf(t7_xboole_0, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.52          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X10 : $i]:
% 0.20/0.52         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.20/0.52      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      ((((sk_B_1) = (k2_subset_1 @ sk_A))
% 0.20/0.52        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1))
% 0.20/0.52         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)))),
% 0.20/0.52      inference('split', [status(esa)], ['8'])).
% 0.20/0.52  thf(t28_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X13 : $i, X14 : $i]:
% 0.20/0.52         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.20/0.52      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      ((((k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)
% 0.20/0.52          = (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.20/0.52         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.52  thf(d4_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.20/0.52       ( ![D:$i]:
% 0.20/0.52         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.52           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X4 @ X3)
% 0.20/0.52          | (r2_hidden @ X4 @ X2)
% 0.20/0.52          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.20/0.52         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      ((![X0 : $i]:
% 0.20/0.52          (~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.20/0.52           | (r2_hidden @ X0 @ sk_B_1)))
% 0.20/0.52         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['11', '13'])).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (((((k3_subset_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.20/0.52         | (r2_hidden @ (sk_B @ (k3_subset_1 @ sk_A @ sk_B_1)) @ sk_B_1)))
% 0.20/0.52         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['7', '14'])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X10 : $i]:
% 0.20/0.52         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.20/0.52      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.52  thf(t3_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.52            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.52       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.52            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X8 @ X6)
% 0.20/0.52          | ~ (r2_hidden @ X8 @ X9)
% 0.20/0.52          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.20/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((X0) = (k1_xboole_0))
% 0.20/0.52          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.20/0.52          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (((((k3_subset_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.20/0.52         | ~ (r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)
% 0.20/0.52         | ((k3_subset_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))
% 0.20/0.52         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['15', '18'])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.52  thf(t79_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X16 : $i, X17 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X17)),
% 0.20/0.52      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (((((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.20/0.52         | ((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))))
% 0.20/0.52         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)))),
% 0.20/0.52      inference('demod', [status(thm)], ['19', '20', '21', '22', '23'])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      ((((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.20/0.52         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      ((((sk_B_1) != (k2_subset_1 @ sk_A))
% 0.20/0.52        | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (~ (((sk_B_1) = (k2_subset_1 @ sk_A))) | 
% 0.20/0.52       ~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 0.20/0.52      inference('split', [status(esa)], ['26'])).
% 0.20/0.52  thf(t4_subset_1, axiom,
% 0.20/0.52    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (![X25 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X25))),
% 0.20/0.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (![X22 : $i, X23 : $i]:
% 0.20/0.52         (((k3_subset_1 @ X23 @ (k3_subset_1 @ X23 @ X22)) = (X22))
% 0.20/0.52          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 0.20/0.52      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.52  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.52  thf('31', plain, (![X18 : $i]: ((k1_subset_1 @ X18) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.20/0.52  thf(t22_subset_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      (![X24 : $i]:
% 0.20/0.52         ((k2_subset_1 @ X24) = (k3_subset_1 @ X24 @ (k1_subset_1 @ X24)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.20/0.52  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.52  thf('33', plain, (![X19 : $i]: ((k2_subset_1 @ X19) = (X19))),
% 0.20/0.52      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      (![X24 : $i]: ((X24) = (k3_subset_1 @ X24 @ (k1_subset_1 @ X24)))),
% 0.20/0.52      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.52  thf('35', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['31', '34'])).
% 0.20/0.52  thf('36', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['30', '35'])).
% 0.20/0.52  thf('37', plain, (![X19 : $i]: ((k2_subset_1 @ X19) = (X19))),
% 0.20/0.52      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      ((((sk_B_1) = (k2_subset_1 @ sk_A)))
% 0.20/0.52         <= ((((sk_B_1) = (k2_subset_1 @ sk_A))))),
% 0.20/0.52      inference('split', [status(esa)], ['8'])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      ((((sk_B_1) = (sk_A))) <= ((((sk_B_1) = (k2_subset_1 @ sk_A))))),
% 0.20/0.52      inference('sup+', [status(thm)], ['37', '38'])).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1))
% 0.20/0.52         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)))),
% 0.20/0.52      inference('split', [status(esa)], ['26'])).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_A))
% 0.20/0.52         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)) & 
% 0.20/0.52             (((sk_B_1) = (k2_subset_1 @ sk_A))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      ((((sk_B_1) = (sk_A))) <= ((((sk_B_1) = (k2_subset_1 @ sk_A))))),
% 0.20/0.52      inference('sup+', [status(thm)], ['37', '38'])).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_A) @ sk_A))
% 0.20/0.52         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)) & 
% 0.20/0.52             (((sk_B_1) = (k2_subset_1 @ sk_A))))),
% 0.20/0.52      inference('demod', [status(thm)], ['41', '42'])).
% 0.20/0.52  thf('44', plain,
% 0.20/0.52      ((~ (r1_tarski @ k1_xboole_0 @ sk_A))
% 0.20/0.52         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)) & 
% 0.20/0.52             (((sk_B_1) = (k2_subset_1 @ sk_A))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['36', '43'])).
% 0.20/0.52  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.52  thf('45', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ X15)),
% 0.20/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)) | 
% 0.20/0.52       ~ (((sk_B_1) = (k2_subset_1 @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['44', '45'])).
% 0.20/0.52  thf('47', plain,
% 0.20/0.52      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)) | 
% 0.20/0.52       (((sk_B_1) = (k2_subset_1 @ sk_A)))),
% 0.20/0.52      inference('split', [status(esa)], ['8'])).
% 0.20/0.52  thf('48', plain, (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['27', '46', '47'])).
% 0.20/0.52  thf('49', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['25', '48'])).
% 0.20/0.52  thf('50', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['31', '34'])).
% 0.20/0.52  thf('51', plain, (((sk_A) = (sk_B_1))),
% 0.20/0.52      inference('demod', [status(thm)], ['6', '49', '50'])).
% 0.20/0.52  thf('52', plain,
% 0.20/0.52      ((((sk_B_1) != (k2_subset_1 @ sk_A)))
% 0.20/0.52         <= (~ (((sk_B_1) = (k2_subset_1 @ sk_A))))),
% 0.20/0.52      inference('split', [status(esa)], ['26'])).
% 0.20/0.52  thf('53', plain, (![X19 : $i]: ((k2_subset_1 @ X19) = (X19))),
% 0.20/0.52      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.52  thf('54', plain,
% 0.20/0.52      ((((sk_B_1) != (sk_A))) <= (~ (((sk_B_1) = (k2_subset_1 @ sk_A))))),
% 0.20/0.52      inference('demod', [status(thm)], ['52', '53'])).
% 0.20/0.52  thf('55', plain, (~ (((sk_B_1) = (k2_subset_1 @ sk_A)))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['27', '46'])).
% 0.20/0.52  thf('56', plain, (((sk_B_1) != (sk_A))),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['54', '55'])).
% 0.20/0.52  thf('57', plain, ($false),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['51', '56'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
