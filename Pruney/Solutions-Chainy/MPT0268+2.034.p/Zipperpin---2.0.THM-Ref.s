%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cIylXRI6ug

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:56 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 144 expanded)
%              Number of leaves         :   23 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :  436 ( 961 expanded)
%              Number of equality atoms :   45 ( 101 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t65_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = A )
      <=> ~ ( r2_hidden @ B @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t65_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('9',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X27 ) @ X28 )
      | ~ ( r2_hidden @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','12'])).

thf('14',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','13'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('15',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('16',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

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
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('22',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X29 ) @ X30 )
      | ( r2_hidden @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t87_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k2_xboole_0 @ ( k4_xboole_0 @ C @ A ) @ B )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ C @ B ) @ A ) ) ) )).

thf('23',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_xboole_0 @ X14 @ X15 )
      | ( ( k2_xboole_0 @ ( k4_xboole_0 @ X16 @ X14 ) @ X15 )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ X16 @ X15 ) @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t87_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k1_tarski @ X1 ) ) @ X0 )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ k1_xboole_0 @ X1 )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('29',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ ( k4_xboole_0 @ X9 @ X10 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('33',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['30','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['30','37'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['25','38','39'])).

thf('41',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('42',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('43',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['2','12','42'])).

thf('44',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['41','43'])).

thf('45',plain,
    ( ( sk_A != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['40','44'])).

thf('46',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['14','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.16  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.17  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cIylXRI6ug
% 0.15/0.39  % Computer   : n011.cluster.edu
% 0.15/0.39  % Model      : x86_64 x86_64
% 0.15/0.39  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.39  % Memory     : 8042.1875MB
% 0.15/0.39  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.39  % CPULimit   : 60
% 0.15/0.39  % DateTime   : Tue Dec  1 18:44:27 EST 2020
% 0.15/0.39  % CPUTime    : 
% 0.15/0.39  % Running portfolio for 600 s
% 0.15/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.40  % Number of cores: 8
% 0.15/0.40  % Python version: Python 3.6.8
% 0.15/0.40  % Running in FO mode
% 0.34/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.34/0.57  % Solved by: fo/fo7.sh
% 0.34/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.57  % done 173 iterations in 0.066s
% 0.34/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.34/0.57  % SZS output start Refutation
% 0.34/0.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.34/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.34/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.34/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.34/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.34/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.34/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.34/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.34/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.34/0.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.34/0.57  thf(t65_zfmisc_1, conjecture,
% 0.34/0.57    (![A:$i,B:$i]:
% 0.34/0.57     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.34/0.57       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.34/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.57    (~( ![A:$i,B:$i]:
% 0.34/0.57        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.34/0.57          ( ~( r2_hidden @ B @ A ) ) ) )),
% 0.34/0.57    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 0.34/0.57  thf('0', plain,
% 0.34/0.57      ((~ (r2_hidden @ sk_B @ sk_A)
% 0.34/0.57        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.34/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.57  thf('1', plain,
% 0.34/0.57      ((~ (r2_hidden @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_B @ sk_A)))),
% 0.34/0.57      inference('split', [status(esa)], ['0'])).
% 0.34/0.57  thf('2', plain,
% 0.34/0.57      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 0.34/0.57       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.34/0.57      inference('split', [status(esa)], ['0'])).
% 0.34/0.57  thf('3', plain,
% 0.34/0.57      (((r2_hidden @ sk_B @ sk_A)
% 0.34/0.57        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))),
% 0.34/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.57  thf('4', plain,
% 0.34/0.57      (((r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.34/0.57      inference('split', [status(esa)], ['3'])).
% 0.34/0.57  thf('5', plain,
% 0.34/0.57      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))
% 0.34/0.57         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.34/0.57      inference('split', [status(esa)], ['0'])).
% 0.34/0.57  thf(t79_xboole_1, axiom,
% 0.34/0.57    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.34/0.57  thf('6', plain,
% 0.34/0.57      (![X12 : $i, X13 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X13)),
% 0.34/0.57      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.34/0.57  thf(symmetry_r1_xboole_0, axiom,
% 0.34/0.57    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.34/0.57  thf('7', plain,
% 0.34/0.57      (![X2 : $i, X3 : $i]:
% 0.34/0.57         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.34/0.57      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.34/0.57  thf('8', plain,
% 0.34/0.57      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.34/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.34/0.57  thf(l24_zfmisc_1, axiom,
% 0.34/0.57    (![A:$i,B:$i]:
% 0.34/0.57     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.34/0.57  thf('9', plain,
% 0.34/0.57      (![X27 : $i, X28 : $i]:
% 0.34/0.57         (~ (r1_xboole_0 @ (k1_tarski @ X27) @ X28) | ~ (r2_hidden @ X27 @ X28))),
% 0.34/0.57      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.34/0.57  thf('10', plain,
% 0.34/0.57      (![X0 : $i, X1 : $i]:
% 0.34/0.57         ~ (r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.34/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.34/0.57  thf('11', plain,
% 0.34/0.57      ((~ (r2_hidden @ sk_B @ sk_A))
% 0.34/0.57         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.34/0.57      inference('sup-', [status(thm)], ['5', '10'])).
% 0.34/0.57  thf('12', plain,
% 0.34/0.57      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 0.34/0.57       ~ ((r2_hidden @ sk_B @ sk_A))),
% 0.34/0.57      inference('sup-', [status(thm)], ['4', '11'])).
% 0.34/0.57  thf('13', plain, (~ ((r2_hidden @ sk_B @ sk_A))),
% 0.34/0.57      inference('sat_resolution*', [status(thm)], ['2', '12'])).
% 0.34/0.57  thf('14', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 0.34/0.57      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.34/0.57  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.34/0.57  thf('15', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.34/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.34/0.57  thf(t28_xboole_1, axiom,
% 0.34/0.57    (![A:$i,B:$i]:
% 0.34/0.57     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.34/0.57  thf('16', plain,
% 0.34/0.57      (![X6 : $i, X7 : $i]:
% 0.34/0.57         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.34/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.34/0.57  thf('17', plain,
% 0.34/0.57      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.34/0.57      inference('sup-', [status(thm)], ['15', '16'])).
% 0.34/0.57  thf(t100_xboole_1, axiom,
% 0.34/0.57    (![A:$i,B:$i]:
% 0.34/0.57     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.34/0.57  thf('18', plain,
% 0.34/0.57      (![X4 : $i, X5 : $i]:
% 0.34/0.57         ((k4_xboole_0 @ X4 @ X5)
% 0.34/0.57           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.34/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.34/0.57  thf('19', plain,
% 0.34/0.57      (![X0 : $i]:
% 0.34/0.57         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.34/0.57           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.34/0.57      inference('sup+', [status(thm)], ['17', '18'])).
% 0.34/0.57  thf(t5_boole, axiom,
% 0.34/0.57    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.34/0.57  thf('20', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.34/0.57      inference('cnf', [status(esa)], [t5_boole])).
% 0.34/0.57  thf('21', plain,
% 0.34/0.57      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.34/0.57      inference('demod', [status(thm)], ['19', '20'])).
% 0.34/0.57  thf(l27_zfmisc_1, axiom,
% 0.34/0.57    (![A:$i,B:$i]:
% 0.34/0.57     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.34/0.57  thf('22', plain,
% 0.34/0.57      (![X29 : $i, X30 : $i]:
% 0.34/0.57         ((r1_xboole_0 @ (k1_tarski @ X29) @ X30) | (r2_hidden @ X29 @ X30))),
% 0.34/0.57      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.34/0.57  thf(t87_xboole_1, axiom,
% 0.34/0.57    (![A:$i,B:$i,C:$i]:
% 0.34/0.57     ( ( r1_xboole_0 @ A @ B ) =>
% 0.34/0.57       ( ( k2_xboole_0 @ ( k4_xboole_0 @ C @ A ) @ B ) =
% 0.34/0.57         ( k4_xboole_0 @ ( k2_xboole_0 @ C @ B ) @ A ) ) ))).
% 0.34/0.57  thf('23', plain,
% 0.34/0.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.34/0.57         (~ (r1_xboole_0 @ X14 @ X15)
% 0.34/0.57          | ((k2_xboole_0 @ (k4_xboole_0 @ X16 @ X14) @ X15)
% 0.34/0.57              = (k4_xboole_0 @ (k2_xboole_0 @ X16 @ X15) @ X14)))),
% 0.34/0.57      inference('cnf', [status(esa)], [t87_xboole_1])).
% 0.34/0.57  thf('24', plain,
% 0.34/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.57         ((r2_hidden @ X1 @ X0)
% 0.34/0.57          | ((k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k1_tarski @ X1)) @ X0)
% 0.34/0.57              = (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ (k1_tarski @ X1))))),
% 0.34/0.57      inference('sup-', [status(thm)], ['22', '23'])).
% 0.34/0.57  thf('25', plain,
% 0.34/0.57      (![X0 : $i, X1 : $i]:
% 0.34/0.57         (((k2_xboole_0 @ k1_xboole_0 @ X1)
% 0.34/0.57            = (k4_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X1) @ 
% 0.34/0.57               (k1_tarski @ X0)))
% 0.34/0.57          | (r2_hidden @ X0 @ X1))),
% 0.34/0.57      inference('sup+', [status(thm)], ['21', '24'])).
% 0.34/0.57  thf('26', plain,
% 0.34/0.57      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.34/0.57      inference('sup-', [status(thm)], ['15', '16'])).
% 0.34/0.57  thf(commutativity_k3_xboole_0, axiom,
% 0.34/0.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.34/0.57  thf('27', plain,
% 0.34/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.34/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.34/0.57  thf('28', plain,
% 0.34/0.57      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.34/0.57      inference('sup+', [status(thm)], ['26', '27'])).
% 0.34/0.57  thf(t51_xboole_1, axiom,
% 0.34/0.57    (![A:$i,B:$i]:
% 0.34/0.57     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.34/0.57       ( A ) ))).
% 0.34/0.57  thf('29', plain,
% 0.34/0.57      (![X9 : $i, X10 : $i]:
% 0.34/0.57         ((k2_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ (k4_xboole_0 @ X9 @ X10))
% 0.34/0.57           = (X9))),
% 0.34/0.57      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.34/0.57  thf('30', plain,
% 0.34/0.57      (![X0 : $i]:
% 0.34/0.57         ((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 0.34/0.57      inference('sup+', [status(thm)], ['28', '29'])).
% 0.34/0.57  thf('31', plain,
% 0.34/0.57      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.34/0.57      inference('sup-', [status(thm)], ['15', '16'])).
% 0.34/0.57  thf('32', plain,
% 0.34/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.34/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.34/0.57  thf('33', plain,
% 0.34/0.57      (![X4 : $i, X5 : $i]:
% 0.34/0.57         ((k4_xboole_0 @ X4 @ X5)
% 0.34/0.57           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.34/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.34/0.57  thf('34', plain,
% 0.34/0.57      (![X0 : $i, X1 : $i]:
% 0.34/0.57         ((k4_xboole_0 @ X0 @ X1)
% 0.34/0.57           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.34/0.57      inference('sup+', [status(thm)], ['32', '33'])).
% 0.34/0.57  thf('35', plain,
% 0.34/0.57      (![X0 : $i]:
% 0.34/0.57         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.34/0.57      inference('sup+', [status(thm)], ['31', '34'])).
% 0.34/0.57  thf('36', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.34/0.57      inference('cnf', [status(esa)], [t5_boole])).
% 0.34/0.57  thf('37', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.34/0.57      inference('demod', [status(thm)], ['35', '36'])).
% 0.34/0.57  thf('38', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.34/0.57      inference('demod', [status(thm)], ['30', '37'])).
% 0.34/0.57  thf('39', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.34/0.57      inference('demod', [status(thm)], ['30', '37'])).
% 0.34/0.57  thf('40', plain,
% 0.34/0.57      (![X0 : $i, X1 : $i]:
% 0.34/0.57         (((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.34/0.57          | (r2_hidden @ X0 @ X1))),
% 0.34/0.57      inference('demod', [status(thm)], ['25', '38', '39'])).
% 0.34/0.57  thf('41', plain,
% 0.34/0.58      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))
% 0.34/0.58         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.34/0.58      inference('split', [status(esa)], ['3'])).
% 0.34/0.58  thf('42', plain,
% 0.34/0.58      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 0.34/0.58       ((r2_hidden @ sk_B @ sk_A))),
% 0.34/0.58      inference('split', [status(esa)], ['3'])).
% 0.34/0.58  thf('43', plain, (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.34/0.58      inference('sat_resolution*', [status(thm)], ['2', '12', '42'])).
% 0.34/0.58  thf('44', plain, (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A))),
% 0.34/0.58      inference('simpl_trail', [status(thm)], ['41', '43'])).
% 0.34/0.58  thf('45', plain, ((((sk_A) != (sk_A)) | (r2_hidden @ sk_B @ sk_A))),
% 0.34/0.58      inference('sup-', [status(thm)], ['40', '44'])).
% 0.34/0.58  thf('46', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.34/0.58      inference('simplify', [status(thm)], ['45'])).
% 0.34/0.58  thf('47', plain, ($false), inference('demod', [status(thm)], ['14', '46'])).
% 0.34/0.58  
% 0.34/0.58  % SZS output end Refutation
% 0.34/0.58  
% 0.34/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
