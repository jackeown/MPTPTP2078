%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zUBi0RiWxU

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:18 EST 2020

% Result     : Theorem 0.88s
% Output     : Refutation 0.88s
% Verified   : 
% Statistics : Number of formulae       :   64 (  81 expanded)
%              Number of leaves         :   17 (  31 expanded)
%              Depth                    :   16
%              Number of atoms          :  512 ( 736 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t57_setfam_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ C @ ( k3_tarski @ ( k2_xboole_0 @ A @ B ) ) )
        & ! [D: $i] :
            ( ( r2_hidden @ D @ B )
           => ( r1_xboole_0 @ D @ C ) ) )
     => ( r1_tarski @ C @ ( k3_tarski @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ C @ ( k3_tarski @ ( k2_xboole_0 @ A @ B ) ) )
          & ! [D: $i] :
              ( ( r2_hidden @ D @ B )
             => ( r1_xboole_0 @ D @ C ) ) )
       => ( r1_tarski @ C @ ( k3_tarski @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t57_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_C_3 @ ( k3_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    r1_tarski @ sk_C_3 @ ( k3_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k3_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_3 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_3 ) @ ( k3_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t96_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('6',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ X14 @ X15 ) )
      = ( k2_xboole_0 @ ( k3_tarski @ X14 ) @ ( k3_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t96_zfmisc_1])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X6
       != ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('8',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_tarski @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ X2 @ ( k3_tarski @ X1 ) )
      | ( r2_hidden @ X2 @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_3 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_3 ) @ ( k3_tarski @ sk_B ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_3 ) @ ( k3_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf(t98_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_xboole_0 @ C @ B ) )
     => ( r1_xboole_0 @ ( k3_tarski @ A ) @ B ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ X16 ) @ X17 )
      | ( r2_hidden @ ( sk_C_2 @ X17 @ X16 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t98_zfmisc_1])).

thf('12',plain,(
    ! [X18: $i] :
      ( ( r1_xboole_0 @ X18 @ sk_C_3 )
      | ~ ( r2_hidden @ X18 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ sk_B ) @ X0 )
      | ( r1_xboole_0 @ ( sk_C_2 @ X0 @ sk_B ) @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ X16 ) @ X17 )
      | ~ ( r1_xboole_0 @ ( sk_C_2 @ X17 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t98_zfmisc_1])).

thf('15',plain,
    ( ( r1_xboole_0 @ ( k3_tarski @ sk_B ) @ sk_C_3 )
    | ( r1_xboole_0 @ ( k3_tarski @ sk_B ) @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r1_xboole_0 @ ( k3_tarski @ sk_B ) @ sk_C_3 ),
    inference(simplify,[status(thm)],['15'])).

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
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k2_xboole_0 @ X0 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k2_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference(eq_fact,[status(thm)],['20'])).

thf('22',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X0 ) @ X0 )
      | ( r1_tarski @ ( k2_xboole_0 @ X0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ ( k2_xboole_0 @ X0 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','26'])).

thf('28',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('29',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_C_3 @ sk_C_3 ) @ ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['16','32'])).

thf('34',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('35',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( X6
       != ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('36',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ ( k2_xboole_0 @ X7 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X2 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ X0 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X0 @ sk_C_3 ) @ ( k3_tarski @ sk_B ) )
      | ( r1_tarski @ sk_C_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_3 ) @ ( k3_tarski @ sk_A ) )
      | ( r1_tarski @ sk_C_3 @ X0 ) ) ),
    inference(clc,[status(thm)],['10','40'])).

thf('42',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('43',plain,
    ( ( r1_tarski @ sk_C_3 @ ( k3_tarski @ sk_A ) )
    | ( r1_tarski @ sk_C_3 @ ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r1_tarski @ sk_C_3 @ ( k3_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['0','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zUBi0RiWxU
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:30:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.88/1.12  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.88/1.12  % Solved by: fo/fo7.sh
% 0.88/1.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.88/1.12  % done 1319 iterations in 0.663s
% 0.88/1.12  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.88/1.12  % SZS output start Refutation
% 0.88/1.12  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.88/1.12  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.88/1.12  thf(sk_A_type, type, sk_A: $i).
% 0.88/1.12  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.88/1.12  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.88/1.12  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.88/1.12  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.88/1.12  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.88/1.12  thf(sk_B_type, type, sk_B: $i).
% 0.88/1.12  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.88/1.12  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.88/1.12  thf(t57_setfam_1, conjecture,
% 0.88/1.12    (![A:$i,B:$i,C:$i]:
% 0.88/1.12     ( ( ( r1_tarski @ C @ ( k3_tarski @ ( k2_xboole_0 @ A @ B ) ) ) & 
% 0.88/1.12         ( ![D:$i]: ( ( r2_hidden @ D @ B ) => ( r1_xboole_0 @ D @ C ) ) ) ) =>
% 0.88/1.12       ( r1_tarski @ C @ ( k3_tarski @ A ) ) ))).
% 0.88/1.12  thf(zf_stmt_0, negated_conjecture,
% 0.88/1.12    (~( ![A:$i,B:$i,C:$i]:
% 0.88/1.12        ( ( ( r1_tarski @ C @ ( k3_tarski @ ( k2_xboole_0 @ A @ B ) ) ) & 
% 0.88/1.12            ( ![D:$i]: ( ( r2_hidden @ D @ B ) => ( r1_xboole_0 @ D @ C ) ) ) ) =>
% 0.88/1.12          ( r1_tarski @ C @ ( k3_tarski @ A ) ) ) )),
% 0.88/1.12    inference('cnf.neg', [status(esa)], [t57_setfam_1])).
% 0.88/1.12  thf('0', plain, (~ (r1_tarski @ sk_C_3 @ (k3_tarski @ sk_A))),
% 0.88/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.12  thf(d3_tarski, axiom,
% 0.88/1.12    (![A:$i,B:$i]:
% 0.88/1.12     ( ( r1_tarski @ A @ B ) <=>
% 0.88/1.12       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.88/1.12  thf('1', plain,
% 0.88/1.12      (![X1 : $i, X3 : $i]:
% 0.88/1.12         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.88/1.12      inference('cnf', [status(esa)], [d3_tarski])).
% 0.88/1.12  thf('2', plain,
% 0.88/1.12      ((r1_tarski @ sk_C_3 @ (k3_tarski @ (k2_xboole_0 @ sk_A @ sk_B)))),
% 0.88/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.12  thf('3', plain,
% 0.88/1.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.88/1.12         (~ (r2_hidden @ X0 @ X1)
% 0.88/1.12          | (r2_hidden @ X0 @ X2)
% 0.88/1.12          | ~ (r1_tarski @ X1 @ X2))),
% 0.88/1.12      inference('cnf', [status(esa)], [d3_tarski])).
% 0.88/1.12  thf('4', plain,
% 0.88/1.12      (![X0 : $i]:
% 0.88/1.12         ((r2_hidden @ X0 @ (k3_tarski @ (k2_xboole_0 @ sk_A @ sk_B)))
% 0.88/1.12          | ~ (r2_hidden @ X0 @ sk_C_3))),
% 0.88/1.12      inference('sup-', [status(thm)], ['2', '3'])).
% 0.88/1.12  thf('5', plain,
% 0.88/1.12      (![X0 : $i]:
% 0.88/1.12         ((r1_tarski @ sk_C_3 @ X0)
% 0.88/1.12          | (r2_hidden @ (sk_C @ X0 @ sk_C_3) @ 
% 0.88/1.12             (k3_tarski @ (k2_xboole_0 @ sk_A @ sk_B))))),
% 0.88/1.12      inference('sup-', [status(thm)], ['1', '4'])).
% 0.88/1.12  thf(t96_zfmisc_1, axiom,
% 0.88/1.12    (![A:$i,B:$i]:
% 0.88/1.12     ( ( k3_tarski @ ( k2_xboole_0 @ A @ B ) ) =
% 0.88/1.12       ( k2_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.88/1.12  thf('6', plain,
% 0.88/1.12      (![X14 : $i, X15 : $i]:
% 0.88/1.12         ((k3_tarski @ (k2_xboole_0 @ X14 @ X15))
% 0.88/1.12           = (k2_xboole_0 @ (k3_tarski @ X14) @ (k3_tarski @ X15)))),
% 0.88/1.12      inference('cnf', [status(esa)], [t96_zfmisc_1])).
% 0.88/1.12  thf(d3_xboole_0, axiom,
% 0.88/1.12    (![A:$i,B:$i,C:$i]:
% 0.88/1.12     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.88/1.12       ( ![D:$i]:
% 0.88/1.12         ( ( r2_hidden @ D @ C ) <=>
% 0.88/1.12           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.88/1.12  thf('7', plain,
% 0.88/1.12      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.88/1.12         (~ (r2_hidden @ X8 @ X6)
% 0.88/1.12          | (r2_hidden @ X8 @ X7)
% 0.88/1.12          | (r2_hidden @ X8 @ X5)
% 0.88/1.12          | ((X6) != (k2_xboole_0 @ X7 @ X5)))),
% 0.88/1.12      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.88/1.12  thf('8', plain,
% 0.88/1.12      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.88/1.12         ((r2_hidden @ X8 @ X5)
% 0.88/1.12          | (r2_hidden @ X8 @ X7)
% 0.88/1.12          | ~ (r2_hidden @ X8 @ (k2_xboole_0 @ X7 @ X5)))),
% 0.88/1.12      inference('simplify', [status(thm)], ['7'])).
% 0.88/1.12  thf('9', plain,
% 0.88/1.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.88/1.12         (~ (r2_hidden @ X2 @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))
% 0.88/1.12          | (r2_hidden @ X2 @ (k3_tarski @ X1))
% 0.88/1.12          | (r2_hidden @ X2 @ (k3_tarski @ X0)))),
% 0.88/1.12      inference('sup-', [status(thm)], ['6', '8'])).
% 0.88/1.12  thf('10', plain,
% 0.88/1.12      (![X0 : $i]:
% 0.88/1.12         ((r1_tarski @ sk_C_3 @ X0)
% 0.88/1.12          | (r2_hidden @ (sk_C @ X0 @ sk_C_3) @ (k3_tarski @ sk_B))
% 0.88/1.12          | (r2_hidden @ (sk_C @ X0 @ sk_C_3) @ (k3_tarski @ sk_A)))),
% 0.88/1.12      inference('sup-', [status(thm)], ['5', '9'])).
% 0.88/1.12  thf(t98_zfmisc_1, axiom,
% 0.88/1.12    (![A:$i,B:$i]:
% 0.88/1.12     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_xboole_0 @ C @ B ) ) ) =>
% 0.88/1.12       ( r1_xboole_0 @ ( k3_tarski @ A ) @ B ) ))).
% 0.88/1.12  thf('11', plain,
% 0.88/1.12      (![X16 : $i, X17 : $i]:
% 0.88/1.12         ((r1_xboole_0 @ (k3_tarski @ X16) @ X17)
% 0.88/1.12          | (r2_hidden @ (sk_C_2 @ X17 @ X16) @ X16))),
% 0.88/1.12      inference('cnf', [status(esa)], [t98_zfmisc_1])).
% 0.88/1.12  thf('12', plain,
% 0.88/1.12      (![X18 : $i]: ((r1_xboole_0 @ X18 @ sk_C_3) | ~ (r2_hidden @ X18 @ sk_B))),
% 0.88/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.12  thf('13', plain,
% 0.88/1.12      (![X0 : $i]:
% 0.88/1.12         ((r1_xboole_0 @ (k3_tarski @ sk_B) @ X0)
% 0.88/1.12          | (r1_xboole_0 @ (sk_C_2 @ X0 @ sk_B) @ sk_C_3))),
% 0.88/1.12      inference('sup-', [status(thm)], ['11', '12'])).
% 0.88/1.12  thf('14', plain,
% 0.88/1.12      (![X16 : $i, X17 : $i]:
% 0.88/1.12         ((r1_xboole_0 @ (k3_tarski @ X16) @ X17)
% 0.88/1.12          | ~ (r1_xboole_0 @ (sk_C_2 @ X17 @ X16) @ X17))),
% 0.88/1.12      inference('cnf', [status(esa)], [t98_zfmisc_1])).
% 0.88/1.12  thf('15', plain,
% 0.88/1.12      (((r1_xboole_0 @ (k3_tarski @ sk_B) @ sk_C_3)
% 0.88/1.12        | (r1_xboole_0 @ (k3_tarski @ sk_B) @ sk_C_3))),
% 0.88/1.12      inference('sup-', [status(thm)], ['13', '14'])).
% 0.88/1.12  thf('16', plain, ((r1_xboole_0 @ (k3_tarski @ sk_B) @ sk_C_3)),
% 0.88/1.12      inference('simplify', [status(thm)], ['15'])).
% 0.88/1.12  thf(t3_xboole_0, axiom,
% 0.88/1.12    (![A:$i,B:$i]:
% 0.88/1.12     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.88/1.12            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.88/1.12       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.88/1.12            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.88/1.12  thf('17', plain,
% 0.88/1.12      (![X10 : $i, X11 : $i]:
% 0.88/1.12         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C_1 @ X11 @ X10) @ X10))),
% 0.88/1.12      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.88/1.12  thf('18', plain,
% 0.88/1.12      (![X1 : $i, X3 : $i]:
% 0.88/1.12         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.88/1.12      inference('cnf', [status(esa)], [d3_tarski])).
% 0.88/1.12  thf('19', plain,
% 0.88/1.12      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.88/1.12         ((r2_hidden @ X8 @ X5)
% 0.88/1.12          | (r2_hidden @ X8 @ X7)
% 0.88/1.12          | ~ (r2_hidden @ X8 @ (k2_xboole_0 @ X7 @ X5)))),
% 0.88/1.12      inference('simplify', [status(thm)], ['7'])).
% 0.88/1.12  thf('20', plain,
% 0.88/1.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.88/1.12         ((r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 0.88/1.12          | (r2_hidden @ (sk_C @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1)
% 0.88/1.12          | (r2_hidden @ (sk_C @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X0))),
% 0.88/1.12      inference('sup-', [status(thm)], ['18', '19'])).
% 0.88/1.12  thf('21', plain,
% 0.88/1.12      (![X0 : $i, X1 : $i]:
% 0.88/1.12         ((r2_hidden @ (sk_C @ X1 @ (k2_xboole_0 @ X0 @ X0)) @ X0)
% 0.88/1.12          | (r1_tarski @ (k2_xboole_0 @ X0 @ X0) @ X1))),
% 0.88/1.12      inference('eq_fact', [status(thm)], ['20'])).
% 0.88/1.12  thf('22', plain,
% 0.88/1.12      (![X1 : $i, X3 : $i]:
% 0.88/1.12         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.88/1.12      inference('cnf', [status(esa)], [d3_tarski])).
% 0.88/1.12  thf('23', plain,
% 0.88/1.12      (![X0 : $i]:
% 0.88/1.12         ((r1_tarski @ (k2_xboole_0 @ X0 @ X0) @ X0)
% 0.88/1.12          | (r1_tarski @ (k2_xboole_0 @ X0 @ X0) @ X0))),
% 0.88/1.12      inference('sup-', [status(thm)], ['21', '22'])).
% 0.88/1.12  thf('24', plain, (![X0 : $i]: (r1_tarski @ (k2_xboole_0 @ X0 @ X0) @ X0)),
% 0.88/1.12      inference('simplify', [status(thm)], ['23'])).
% 0.88/1.12  thf('25', plain,
% 0.88/1.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.88/1.12         (~ (r2_hidden @ X0 @ X1)
% 0.88/1.12          | (r2_hidden @ X0 @ X2)
% 0.88/1.12          | ~ (r1_tarski @ X1 @ X2))),
% 0.88/1.12      inference('cnf', [status(esa)], [d3_tarski])).
% 0.88/1.12  thf('26', plain,
% 0.88/1.12      (![X0 : $i, X1 : $i]:
% 0.88/1.12         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ (k2_xboole_0 @ X0 @ X0)))),
% 0.88/1.12      inference('sup-', [status(thm)], ['24', '25'])).
% 0.88/1.12  thf('27', plain,
% 0.88/1.12      (![X0 : $i, X1 : $i]:
% 0.88/1.12         ((r1_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X1)
% 0.88/1.12          | (r2_hidden @ (sk_C_1 @ X1 @ (k2_xboole_0 @ X0 @ X0)) @ X0))),
% 0.88/1.12      inference('sup-', [status(thm)], ['17', '26'])).
% 0.88/1.12  thf('28', plain,
% 0.88/1.12      (![X10 : $i, X11 : $i]:
% 0.88/1.12         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C_1 @ X11 @ X10) @ X11))),
% 0.88/1.12      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.88/1.12  thf('29', plain,
% 0.88/1.12      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.88/1.12         (~ (r2_hidden @ X12 @ X10)
% 0.88/1.12          | ~ (r2_hidden @ X12 @ X13)
% 0.88/1.12          | ~ (r1_xboole_0 @ X10 @ X13))),
% 0.88/1.12      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.88/1.12  thf('30', plain,
% 0.88/1.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.88/1.12         ((r1_xboole_0 @ X1 @ X0)
% 0.88/1.12          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.88/1.12          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 0.88/1.12      inference('sup-', [status(thm)], ['28', '29'])).
% 0.88/1.12  thf('31', plain,
% 0.88/1.12      (![X0 : $i, X1 : $i]:
% 0.88/1.12         ((r1_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X1)
% 0.88/1.12          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.88/1.12          | (r1_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X1))),
% 0.88/1.12      inference('sup-', [status(thm)], ['27', '30'])).
% 0.88/1.12  thf('32', plain,
% 0.88/1.12      (![X0 : $i, X1 : $i]:
% 0.88/1.12         (~ (r1_xboole_0 @ X1 @ X0)
% 0.88/1.12          | (r1_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X1))),
% 0.88/1.12      inference('simplify', [status(thm)], ['31'])).
% 0.88/1.12  thf('33', plain,
% 0.88/1.12      ((r1_xboole_0 @ (k2_xboole_0 @ sk_C_3 @ sk_C_3) @ (k3_tarski @ sk_B))),
% 0.88/1.12      inference('sup-', [status(thm)], ['16', '32'])).
% 0.88/1.12  thf('34', plain,
% 0.88/1.12      (![X1 : $i, X3 : $i]:
% 0.88/1.12         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.88/1.12      inference('cnf', [status(esa)], [d3_tarski])).
% 0.88/1.12  thf('35', plain,
% 0.88/1.12      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.88/1.12         (~ (r2_hidden @ X4 @ X5)
% 0.88/1.12          | (r2_hidden @ X4 @ X6)
% 0.88/1.12          | ((X6) != (k2_xboole_0 @ X7 @ X5)))),
% 0.88/1.12      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.88/1.12  thf('36', plain,
% 0.88/1.12      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.88/1.12         ((r2_hidden @ X4 @ (k2_xboole_0 @ X7 @ X5)) | ~ (r2_hidden @ X4 @ X5))),
% 0.88/1.12      inference('simplify', [status(thm)], ['35'])).
% 0.88/1.12  thf('37', plain,
% 0.88/1.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.88/1.12         ((r1_tarski @ X0 @ X1)
% 0.88/1.12          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_xboole_0 @ X2 @ X0)))),
% 0.88/1.12      inference('sup-', [status(thm)], ['34', '36'])).
% 0.88/1.12  thf('38', plain,
% 0.88/1.12      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.88/1.12         (~ (r2_hidden @ X12 @ X10)
% 0.88/1.12          | ~ (r2_hidden @ X12 @ X13)
% 0.88/1.12          | ~ (r1_xboole_0 @ X10 @ X13))),
% 0.88/1.12      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.88/1.12  thf('39', plain,
% 0.88/1.12      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.88/1.12         ((r1_tarski @ X0 @ X2)
% 0.88/1.12          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X3)
% 0.88/1.12          | ~ (r2_hidden @ (sk_C @ X2 @ X0) @ X3))),
% 0.88/1.12      inference('sup-', [status(thm)], ['37', '38'])).
% 0.88/1.12  thf('40', plain,
% 0.88/1.12      (![X0 : $i]:
% 0.88/1.12         (~ (r2_hidden @ (sk_C @ X0 @ sk_C_3) @ (k3_tarski @ sk_B))
% 0.88/1.12          | (r1_tarski @ sk_C_3 @ X0))),
% 0.88/1.12      inference('sup-', [status(thm)], ['33', '39'])).
% 0.88/1.12  thf('41', plain,
% 0.88/1.12      (![X0 : $i]:
% 0.88/1.12         ((r2_hidden @ (sk_C @ X0 @ sk_C_3) @ (k3_tarski @ sk_A))
% 0.88/1.12          | (r1_tarski @ sk_C_3 @ X0))),
% 0.88/1.12      inference('clc', [status(thm)], ['10', '40'])).
% 0.88/1.12  thf('42', plain,
% 0.88/1.12      (![X1 : $i, X3 : $i]:
% 0.88/1.12         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.88/1.12      inference('cnf', [status(esa)], [d3_tarski])).
% 0.88/1.12  thf('43', plain,
% 0.88/1.12      (((r1_tarski @ sk_C_3 @ (k3_tarski @ sk_A))
% 0.88/1.12        | (r1_tarski @ sk_C_3 @ (k3_tarski @ sk_A)))),
% 0.88/1.12      inference('sup-', [status(thm)], ['41', '42'])).
% 0.88/1.12  thf('44', plain, ((r1_tarski @ sk_C_3 @ (k3_tarski @ sk_A))),
% 0.88/1.12      inference('simplify', [status(thm)], ['43'])).
% 0.88/1.12  thf('45', plain, ($false), inference('demod', [status(thm)], ['0', '44'])).
% 0.88/1.12  
% 0.88/1.12  % SZS output end Refutation
% 0.88/1.12  
% 0.88/1.13  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
