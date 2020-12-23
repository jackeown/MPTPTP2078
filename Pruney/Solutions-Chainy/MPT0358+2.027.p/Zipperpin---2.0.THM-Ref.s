%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tBqwuXvver

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:25 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 155 expanded)
%              Number of leaves         :   21 (  49 expanded)
%              Depth                    :   16
%              Number of atoms          :  422 (1244 expanded)
%              Number of equality atoms :   44 ( 136 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t38_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
        <=> ( B
            = ( k1_subset_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_subset_1])).

thf('1',plain,
    ( ( sk_B_1
      = ( k1_subset_1 @ sk_A ) )
    | ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X18: $i] :
      ( ( k1_subset_1 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('6',plain,
    ( ( sk_B_1
      = ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('7',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('9',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('11',plain,(
    ! [X13: $i] :
      ( r1_tarski @ k1_xboole_0 @ X13 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('12',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('14',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['4','12','13'])).

thf('15',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['2','14'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('16',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('17',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('18',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('19',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('21',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('22',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','23'])).

thf('25',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('26',plain,(
    ! [X18: $i] :
      ( ( k1_subset_1 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('27',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    sk_B_1
 != ( k1_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['4','12'])).

thf('29',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['24','29'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('31',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('32',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('33',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['34'])).

thf('36',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['30','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('38',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('39',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','42'])).

thf('44',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['27','28'])).

thf('45',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['43','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tBqwuXvver
% 0.14/0.37  % Computer   : n021.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 18:30:20 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.37/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.55  % Solved by: fo/fo7.sh
% 0.37/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.55  % done 135 iterations in 0.061s
% 0.37/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.55  % SZS output start Refutation
% 0.37/0.55  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.37/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.37/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.55  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.37/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.37/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.55  thf(t7_xboole_0, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.37/0.55          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.37/0.55  thf('0', plain,
% 0.37/0.55      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.37/0.55      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.37/0.55  thf(t38_subset_1, conjecture,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.55       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.37/0.55         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.37/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.55    (~( ![A:$i,B:$i]:
% 0.37/0.55        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.55          ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.37/0.55            ( ( B ) = ( k1_subset_1 @ A ) ) ) ) )),
% 0.37/0.55    inference('cnf.neg', [status(esa)], [t38_subset_1])).
% 0.37/0.55  thf('1', plain,
% 0.37/0.55      ((((sk_B_1) = (k1_subset_1 @ sk_A))
% 0.37/0.55        | (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('2', plain,
% 0.37/0.55      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.37/0.55         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.37/0.55      inference('split', [status(esa)], ['1'])).
% 0.37/0.55  thf('3', plain,
% 0.37/0.55      ((((sk_B_1) != (k1_subset_1 @ sk_A))
% 0.37/0.55        | ~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('4', plain,
% 0.37/0.55      (~ (((sk_B_1) = (k1_subset_1 @ sk_A))) | 
% 0.37/0.55       ~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.37/0.55      inference('split', [status(esa)], ['3'])).
% 0.37/0.55  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.37/0.55  thf('5', plain, (![X18 : $i]: ((k1_subset_1 @ X18) = (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.37/0.55  thf('6', plain,
% 0.37/0.55      ((((sk_B_1) = (k1_subset_1 @ sk_A)))
% 0.37/0.55         <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.37/0.55      inference('split', [status(esa)], ['1'])).
% 0.37/0.55  thf('7', plain,
% 0.37/0.55      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.37/0.55      inference('sup+', [status(thm)], ['5', '6'])).
% 0.37/0.55  thf('8', plain,
% 0.37/0.55      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.37/0.55         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.37/0.55      inference('split', [status(esa)], ['3'])).
% 0.37/0.55  thf('9', plain,
% 0.37/0.55      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.37/0.55         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.37/0.55             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.37/0.55  thf('10', plain,
% 0.37/0.55      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.37/0.55      inference('sup+', [status(thm)], ['5', '6'])).
% 0.37/0.55  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.37/0.55  thf('11', plain, (![X13 : $i]: (r1_tarski @ k1_xboole_0 @ X13)),
% 0.37/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.55  thf('12', plain,
% 0.37/0.55      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.37/0.55       ~ (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.37/0.55      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.37/0.55  thf('13', plain,
% 0.37/0.55      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.37/0.55       (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.37/0.55      inference('split', [status(esa)], ['1'])).
% 0.37/0.55  thf('14', plain, (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.37/0.55      inference('sat_resolution*', [status(thm)], ['4', '12', '13'])).
% 0.37/0.55  thf('15', plain, ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.37/0.55      inference('simpl_trail', [status(thm)], ['2', '14'])).
% 0.37/0.55  thf(t12_xboole_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.37/0.55  thf('16', plain,
% 0.37/0.55      (![X11 : $i, X12 : $i]:
% 0.37/0.55         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 0.37/0.55      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.37/0.55  thf('17', plain,
% 0.37/0.55      (((k2_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.37/0.55         = (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.37/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.37/0.55  thf(t46_xboole_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.37/0.55  thf('18', plain,
% 0.37/0.55      (![X15 : $i, X16 : $i]:
% 0.37/0.55         ((k4_xboole_0 @ X15 @ (k2_xboole_0 @ X15 @ X16)) = (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.37/0.55  thf('19', plain,
% 0.37/0.55      (((k4_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['17', '18'])).
% 0.37/0.55  thf('20', plain,
% 0.37/0.55      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.37/0.55      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.37/0.55  thf(d5_xboole_0, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.37/0.55       ( ![D:$i]:
% 0.37/0.55         ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.55           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.37/0.55  thf('21', plain,
% 0.37/0.55      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X2 @ X3)
% 0.37/0.55          | (r2_hidden @ X2 @ X4)
% 0.37/0.55          | (r2_hidden @ X2 @ X5)
% 0.37/0.55          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.37/0.55  thf('22', plain,
% 0.37/0.55      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.55         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 0.37/0.55          | (r2_hidden @ X2 @ X4)
% 0.37/0.55          | ~ (r2_hidden @ X2 @ X3))),
% 0.37/0.55      inference('simplify', [status(thm)], ['21'])).
% 0.37/0.55  thf('23', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (((X0) = (k1_xboole_0))
% 0.37/0.55          | (r2_hidden @ (sk_B @ X0) @ X1)
% 0.37/0.55          | (r2_hidden @ (sk_B @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['20', '22'])).
% 0.37/0.55  thf('24', plain,
% 0.37/0.55      (((r2_hidden @ (sk_B @ sk_B_1) @ k1_xboole_0)
% 0.37/0.55        | (r2_hidden @ (sk_B @ sk_B_1) @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.37/0.55        | ((sk_B_1) = (k1_xboole_0)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['19', '23'])).
% 0.37/0.55  thf('25', plain,
% 0.37/0.55      ((((sk_B_1) != (k1_subset_1 @ sk_A)))
% 0.37/0.55         <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.37/0.55      inference('split', [status(esa)], ['3'])).
% 0.37/0.55  thf('26', plain, (![X18 : $i]: ((k1_subset_1 @ X18) = (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.37/0.55  thf('27', plain,
% 0.37/0.55      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.37/0.55      inference('demod', [status(thm)], ['25', '26'])).
% 0.37/0.55  thf('28', plain, (~ (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.37/0.55      inference('sat_resolution*', [status(thm)], ['4', '12'])).
% 0.37/0.55  thf('29', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.37/0.55      inference('simpl_trail', [status(thm)], ['27', '28'])).
% 0.37/0.55  thf('30', plain,
% 0.37/0.55      (((r2_hidden @ (sk_B @ sk_B_1) @ k1_xboole_0)
% 0.37/0.55        | (r2_hidden @ (sk_B @ sk_B_1) @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.37/0.55      inference('simplify_reflect-', [status(thm)], ['24', '29'])).
% 0.37/0.55  thf(t3_boole, axiom,
% 0.37/0.55    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.55  thf('31', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.37/0.55      inference('cnf', [status(esa)], [t3_boole])).
% 0.37/0.55  thf('32', plain,
% 0.37/0.55      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X6 @ X5)
% 0.37/0.55          | ~ (r2_hidden @ X6 @ X4)
% 0.37/0.55          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.37/0.55  thf('33', plain,
% 0.37/0.55      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X6 @ X4)
% 0.37/0.55          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['32'])).
% 0.37/0.55  thf('34', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['31', '33'])).
% 0.37/0.55  thf('35', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.37/0.55      inference('condensation', [status(thm)], ['34'])).
% 0.37/0.55  thf('36', plain,
% 0.37/0.55      ((r2_hidden @ (sk_B @ sk_B_1) @ (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.37/0.55      inference('clc', [status(thm)], ['30', '35'])).
% 0.37/0.55  thf('37', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(d5_subset_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.55       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.37/0.55  thf('38', plain,
% 0.37/0.55      (![X19 : $i, X20 : $i]:
% 0.37/0.55         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 0.37/0.55          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.37/0.55  thf('39', plain,
% 0.37/0.55      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.37/0.55      inference('sup-', [status(thm)], ['37', '38'])).
% 0.37/0.55  thf('40', plain,
% 0.37/0.55      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X6 @ X4)
% 0.37/0.55          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['32'])).
% 0.37/0.55  thf('41', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.37/0.55          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.37/0.55      inference('sup-', [status(thm)], ['39', '40'])).
% 0.37/0.55  thf('42', plain, (~ (r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1)),
% 0.37/0.55      inference('sup-', [status(thm)], ['36', '41'])).
% 0.37/0.55  thf('43', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['0', '42'])).
% 0.37/0.55  thf('44', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.37/0.55      inference('simpl_trail', [status(thm)], ['27', '28'])).
% 0.37/0.55  thf('45', plain, ($false),
% 0.37/0.55      inference('simplify_reflect-', [status(thm)], ['43', '44'])).
% 0.37/0.55  
% 0.37/0.55  % SZS output end Refutation
% 0.37/0.55  
% 0.37/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
