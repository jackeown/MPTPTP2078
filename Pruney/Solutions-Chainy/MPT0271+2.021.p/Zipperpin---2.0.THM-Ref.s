%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mHZpE6q8cl

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 158 expanded)
%              Number of leaves         :   23 (  55 expanded)
%              Depth                    :   12
%              Number of atoms          :  531 (1110 expanded)
%              Number of equality atoms :   51 ( 103 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t68_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = k1_xboole_0 )
      <=> ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t68_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('2',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('7',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_xboole_0 @ X2 @ X4 )
      | ( X2 = X4 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ( r2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t62_xboole_1,axiom,(
    ! [A: $i] :
      ~ ( r2_xboole_0 @ A @ k1_xboole_0 ) )).

thf('9',plain,(
    ! [X12: $i] :
      ~ ( r2_xboole_0 @ X12 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t62_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf(t67_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('15',plain,(
    ! [X21: $i,X23: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X21 ) @ X23 )
        = ( k1_tarski @ X21 ) )
      | ( r2_hidden @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t67_zfmisc_1])).

thf('16',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','17'])).

thf('19',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t6_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf('21',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X25 = X24 )
      | ~ ( r1_tarski @ ( k1_tarski @ X25 ) @ ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t6_zfmisc_1])).

thf('22',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        | ( sk_A = X0 ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ! [X0: $i] : ( sk_A = X0 )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','22'])).

thf('24',plain,
    ( ! [X0: $i] : ( sk_A = X0 )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','22'])).

thf(t50_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
     != k1_xboole_0 ) )).

thf('25',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X18 @ X19 ) @ X20 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t50_zfmisc_1])).

thf('26',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ! [X0: $i] : ( X0 != k1_xboole_0 )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('30',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['16'])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('31',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X17 ) @ X16 )
        = X16 )
      | ~ ( r2_hidden @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('32',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('34',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('36',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      | ~ ( r1_tarski @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ k1_xboole_0 )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('41',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ k1_xboole_0 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ X0 )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_xboole_0 @ X2 @ X4 )
      | ( X2 = X4 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
          = X0 )
        | ( r2_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ X0 ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X12: $i] :
      ~ ( r2_xboole_0 @ X12 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t62_xboole_1])).

thf('48',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('50',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
       != k1_xboole_0 )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','28','29','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mHZpE6q8cl
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:30:40 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.56  % Solved by: fo/fo7.sh
% 0.22/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.56  % done 216 iterations in 0.096s
% 0.22/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.56  % SZS output start Refutation
% 0.22/0.56  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.22/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.56  thf(t68_zfmisc_1, conjecture,
% 0.22/0.56    (![A:$i,B:$i]:
% 0.22/0.56     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.56       ( r2_hidden @ A @ B ) ))).
% 0.22/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.56    (~( ![A:$i,B:$i]:
% 0.22/0.56        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.56          ( r2_hidden @ A @ B ) ) )),
% 0.22/0.56    inference('cnf.neg', [status(esa)], [t68_zfmisc_1])).
% 0.22/0.56  thf('0', plain,
% 0.22/0.56      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.22/0.56        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('1', plain,
% 0.22/0.56      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.22/0.56       ~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.22/0.56      inference('split', [status(esa)], ['0'])).
% 0.22/0.56  thf(t1_boole, axiom,
% 0.22/0.56    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.56  thf('2', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.22/0.56      inference('cnf', [status(esa)], [t1_boole])).
% 0.22/0.56  thf(t7_xboole_1, axiom,
% 0.22/0.56    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.56  thf('3', plain,
% 0.22/0.56      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 0.22/0.56      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.22/0.56  thf('4', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.22/0.56      inference('sup+', [status(thm)], ['2', '3'])).
% 0.22/0.56  thf(t18_xboole_1, axiom,
% 0.22/0.56    (![A:$i,B:$i,C:$i]:
% 0.22/0.56     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 0.22/0.56  thf('5', plain,
% 0.22/0.56      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.56         ((r1_tarski @ X5 @ X6) | ~ (r1_tarski @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.22/0.56      inference('cnf', [status(esa)], [t18_xboole_1])).
% 0.22/0.56  thf('6', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.22/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.56  thf(d8_xboole_0, axiom,
% 0.22/0.56    (![A:$i,B:$i]:
% 0.22/0.56     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.22/0.56       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.22/0.56  thf('7', plain,
% 0.22/0.56      (![X2 : $i, X4 : $i]:
% 0.22/0.56         ((r2_xboole_0 @ X2 @ X4) | ((X2) = (X4)) | ~ (r1_tarski @ X2 @ X4))),
% 0.22/0.56      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.22/0.56  thf('8', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i]:
% 0.22/0.56         (((k3_xboole_0 @ X0 @ X1) = (X0))
% 0.22/0.56          | (r2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.22/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.56  thf(t62_xboole_1, axiom, (![A:$i]: ( ~( r2_xboole_0 @ A @ k1_xboole_0 ) ))).
% 0.22/0.56  thf('9', plain, (![X12 : $i]: ~ (r2_xboole_0 @ X12 @ k1_xboole_0)),
% 0.22/0.56      inference('cnf', [status(esa)], [t62_xboole_1])).
% 0.22/0.56  thf('10', plain,
% 0.22/0.56      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.22/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.56  thf(commutativity_k3_xboole_0, axiom,
% 0.22/0.56    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.22/0.56  thf('11', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.56  thf('12', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.22/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.56  thf('13', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.22/0.56      inference('sup+', [status(thm)], ['11', '12'])).
% 0.22/0.56  thf('14', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.56      inference('sup+', [status(thm)], ['10', '13'])).
% 0.22/0.56  thf(t67_zfmisc_1, axiom,
% 0.22/0.56    (![A:$i,B:$i]:
% 0.22/0.56     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.22/0.56       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.22/0.56  thf('15', plain,
% 0.22/0.56      (![X21 : $i, X23 : $i]:
% 0.22/0.56         (((k4_xboole_0 @ (k1_tarski @ X21) @ X23) = (k1_tarski @ X21))
% 0.22/0.56          | (r2_hidden @ X21 @ X23))),
% 0.22/0.56      inference('cnf', [status(esa)], [t67_zfmisc_1])).
% 0.22/0.56  thf('16', plain,
% 0.22/0.56      (((r2_hidden @ sk_A @ sk_B)
% 0.22/0.56        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('17', plain,
% 0.22/0.56      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))
% 0.22/0.56         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.22/0.56      inference('split', [status(esa)], ['16'])).
% 0.22/0.56  thf('18', plain,
% 0.22/0.56      (((((k1_tarski @ sk_A) = (k1_xboole_0)) | (r2_hidden @ sk_A @ sk_B)))
% 0.22/0.56         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.22/0.56      inference('sup+', [status(thm)], ['15', '17'])).
% 0.22/0.56  thf('19', plain,
% 0.22/0.56      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.56      inference('split', [status(esa)], ['0'])).
% 0.22/0.56  thf('20', plain,
% 0.22/0.56      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.22/0.56         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.22/0.56             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.22/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.56  thf(t6_zfmisc_1, axiom,
% 0.22/0.56    (![A:$i,B:$i]:
% 0.22/0.56     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.22/0.56       ( ( A ) = ( B ) ) ))).
% 0.22/0.56  thf('21', plain,
% 0.22/0.56      (![X24 : $i, X25 : $i]:
% 0.22/0.56         (((X25) = (X24))
% 0.22/0.56          | ~ (r1_tarski @ (k1_tarski @ X25) @ (k1_tarski @ X24)))),
% 0.22/0.56      inference('cnf', [status(esa)], [t6_zfmisc_1])).
% 0.22/0.56  thf('22', plain,
% 0.22/0.56      ((![X0 : $i]:
% 0.22/0.56          (~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) | ((sk_A) = (X0))))
% 0.22/0.56         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.22/0.56             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.22/0.56      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.56  thf('23', plain,
% 0.22/0.56      ((![X0 : $i]: ((sk_A) = (X0)))
% 0.22/0.56         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.22/0.56             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.22/0.56      inference('sup-', [status(thm)], ['14', '22'])).
% 0.22/0.56  thf('24', plain,
% 0.22/0.56      ((![X0 : $i]: ((sk_A) = (X0)))
% 0.22/0.56         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.22/0.56             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.22/0.56      inference('sup-', [status(thm)], ['14', '22'])).
% 0.22/0.56  thf(t50_zfmisc_1, axiom,
% 0.22/0.56    (![A:$i,B:$i,C:$i]:
% 0.22/0.56     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.22/0.56  thf('25', plain,
% 0.22/0.56      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.56         ((k2_xboole_0 @ (k2_tarski @ X18 @ X19) @ X20) != (k1_xboole_0))),
% 0.22/0.56      inference('cnf', [status(esa)], [t50_zfmisc_1])).
% 0.22/0.56  thf('26', plain,
% 0.22/0.56      ((((sk_A) != (k1_xboole_0)))
% 0.22/0.56         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.22/0.56             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.22/0.56      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.56  thf('27', plain,
% 0.22/0.56      ((![X0 : $i]: ((X0) != (k1_xboole_0)))
% 0.22/0.56         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.22/0.56             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.22/0.56      inference('sup-', [status(thm)], ['23', '26'])).
% 0.22/0.56  thf('28', plain,
% 0.22/0.56      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.22/0.56       ~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.22/0.56      inference('simplify', [status(thm)], ['27'])).
% 0.22/0.56  thf('29', plain,
% 0.22/0.56      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.22/0.56       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.22/0.56      inference('split', [status(esa)], ['16'])).
% 0.22/0.56  thf('30', plain,
% 0.22/0.56      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.56      inference('split', [status(esa)], ['16'])).
% 0.22/0.56  thf(l22_zfmisc_1, axiom,
% 0.22/0.56    (![A:$i,B:$i]:
% 0.22/0.56     ( ( r2_hidden @ A @ B ) =>
% 0.22/0.56       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.22/0.56  thf('31', plain,
% 0.22/0.56      (![X16 : $i, X17 : $i]:
% 0.22/0.56         (((k2_xboole_0 @ (k1_tarski @ X17) @ X16) = (X16))
% 0.22/0.56          | ~ (r2_hidden @ X17 @ X16))),
% 0.22/0.56      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.22/0.56  thf('32', plain,
% 0.22/0.56      ((((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B)))
% 0.22/0.56         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.56  thf('33', plain,
% 0.22/0.56      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 0.22/0.56      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.22/0.56  thf('34', plain,
% 0.22/0.56      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B))
% 0.22/0.56         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.56      inference('sup+', [status(thm)], ['32', '33'])).
% 0.22/0.56  thf('35', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.22/0.56      inference('cnf', [status(esa)], [t1_boole])).
% 0.22/0.56  thf(t43_xboole_1, axiom,
% 0.22/0.56    (![A:$i,B:$i,C:$i]:
% 0.22/0.56     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.22/0.56       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.22/0.56  thf('36', plain,
% 0.22/0.56      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.56         ((r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.22/0.56          | ~ (r1_tarski @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.22/0.56      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.22/0.56  thf('37', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i]:
% 0.22/0.56         (~ (r1_tarski @ X1 @ X0)
% 0.22/0.56          | (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 0.22/0.56      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.56  thf('38', plain,
% 0.22/0.56      (((r1_tarski @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ k1_xboole_0))
% 0.22/0.56         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['34', '37'])).
% 0.22/0.56  thf('39', plain,
% 0.22/0.56      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.22/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.56  thf('40', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.56  thf('41', plain,
% 0.22/0.56      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.56         ((r1_tarski @ X5 @ X6) | ~ (r1_tarski @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.22/0.56      inference('cnf', [status(esa)], [t18_xboole_1])).
% 0.22/0.56  thf('42', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.56         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 0.22/0.56      inference('sup-', [status(thm)], ['40', '41'])).
% 0.22/0.56  thf('43', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i]:
% 0.22/0.56         (~ (r1_tarski @ X1 @ k1_xboole_0) | (r1_tarski @ X1 @ X0))),
% 0.22/0.56      inference('sup-', [status(thm)], ['39', '42'])).
% 0.22/0.56  thf('44', plain,
% 0.22/0.56      ((![X0 : $i]:
% 0.22/0.56          (r1_tarski @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ X0))
% 0.22/0.56         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['38', '43'])).
% 0.22/0.56  thf('45', plain,
% 0.22/0.56      (![X2 : $i, X4 : $i]:
% 0.22/0.56         ((r2_xboole_0 @ X2 @ X4) | ((X2) = (X4)) | ~ (r1_tarski @ X2 @ X4))),
% 0.22/0.56      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.22/0.56  thf('46', plain,
% 0.22/0.56      ((![X0 : $i]:
% 0.22/0.56          (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (X0))
% 0.22/0.56           | (r2_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ X0)))
% 0.22/0.56         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['44', '45'])).
% 0.22/0.56  thf('47', plain, (![X12 : $i]: ~ (r2_xboole_0 @ X12 @ k1_xboole_0)),
% 0.22/0.56      inference('cnf', [status(esa)], [t62_xboole_1])).
% 0.22/0.56  thf('48', plain,
% 0.22/0.56      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))
% 0.22/0.56         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['46', '47'])).
% 0.22/0.56  thf('49', plain,
% 0.22/0.56      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))
% 0.22/0.56         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.22/0.56      inference('split', [status(esa)], ['0'])).
% 0.22/0.56  thf('50', plain,
% 0.22/0.56      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.22/0.56         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) & 
% 0.22/0.56             ((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['48', '49'])).
% 0.22/0.56  thf('51', plain,
% 0.22/0.56      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.22/0.56       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.22/0.56      inference('simplify', [status(thm)], ['50'])).
% 0.22/0.56  thf('52', plain, ($false),
% 0.22/0.56      inference('sat_resolution*', [status(thm)], ['1', '28', '29', '51'])).
% 0.22/0.56  
% 0.22/0.56  % SZS output end Refutation
% 0.22/0.56  
% 0.41/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
