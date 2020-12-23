%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.npuEPZo0Nd

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 117 expanded)
%              Number of leaves         :   18 (  38 expanded)
%              Depth                    :   16
%              Number of atoms          :  390 ( 931 expanded)
%              Number of equality atoms :   32 (  86 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t151_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( ( k9_relat_1 @ B @ A )
            = k1_xboole_0 )
        <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t151_relat_1])).

thf('0',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k9_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k9_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k9_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf(t95_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X7 ) @ X8 )
      | ( ( k7_relat_1 @ X7 @ X8 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('6',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( ( k7_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) )
        = ( k9_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('10',plain,
    ( ( ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ sk_B @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('11',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('12',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k1_xboole_0
      = ( k9_relat_1 @ sk_B @ sk_A ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k9_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('15',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k9_relat_1 @ sk_B @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','16'])).

thf('18',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','17'])).

thf('19',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k9_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('20',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('21',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','16','20'])).

thf('22',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['19','21'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('24',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) )
        = ( k9_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('25',plain,(
    ! [X4: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X4 ) )
      | ~ ( v1_relat_1 @ X4 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_xboole_0 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_xboole_0 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ( v1_xboole_0 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( v1_xboole_0 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('30',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('31',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_xboole_0 @ ( k7_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k7_relat_1 @ X7 @ X8 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ X2 @ X1 )
       != X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X2 ) @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_xboole_0 @ ( k7_relat_1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['32','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['18','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.npuEPZo0Nd
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:57:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.21/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.59  % Solved by: fo/fo7.sh
% 0.21/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.59  % done 343 iterations in 0.143s
% 0.21/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.59  % SZS output start Refutation
% 0.21/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.59  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.59  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.59  thf(t151_relat_1, conjecture,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( v1_relat_1 @ B ) =>
% 0.21/0.59       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.59         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.59    (~( ![A:$i,B:$i]:
% 0.21/0.59        ( ( v1_relat_1 @ B ) =>
% 0.21/0.59          ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.59            ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 0.21/0.59    inference('cnf.neg', [status(esa)], [t151_relat_1])).
% 0.21/0.59  thf('0', plain,
% 0.21/0.59      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.21/0.59        | ((k9_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('1', plain,
% 0.21/0.59      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.21/0.59         <= (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.21/0.59      inference('split', [status(esa)], ['0'])).
% 0.21/0.59  thf('2', plain,
% 0.21/0.59      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.21/0.59       ~ (((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.21/0.59      inference('split', [status(esa)], ['0'])).
% 0.21/0.59  thf('3', plain,
% 0.21/0.59      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.21/0.59        | ((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('4', plain,
% 0.21/0.59      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.21/0.59         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.21/0.59      inference('split', [status(esa)], ['3'])).
% 0.21/0.59  thf(t95_relat_1, axiom,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( v1_relat_1 @ B ) =>
% 0.21/0.59       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.59         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.59  thf('5', plain,
% 0.21/0.59      (![X7 : $i, X8 : $i]:
% 0.21/0.59         (~ (r1_xboole_0 @ (k1_relat_1 @ X7) @ X8)
% 0.21/0.59          | ((k7_relat_1 @ X7 @ X8) = (k1_xboole_0))
% 0.21/0.59          | ~ (v1_relat_1 @ X7))),
% 0.21/0.59      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.21/0.59  thf('6', plain,
% 0.21/0.59      (((~ (v1_relat_1 @ sk_B) | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))
% 0.21/0.59         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.59  thf('7', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('8', plain,
% 0.21/0.59      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.21/0.59         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.21/0.59      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.59  thf(t148_relat_1, axiom,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( v1_relat_1 @ B ) =>
% 0.21/0.59       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.21/0.59  thf('9', plain,
% 0.21/0.59      (![X5 : $i, X6 : $i]:
% 0.21/0.59         (((k2_relat_1 @ (k7_relat_1 @ X5 @ X6)) = (k9_relat_1 @ X5 @ X6))
% 0.21/0.59          | ~ (v1_relat_1 @ X5))),
% 0.21/0.59      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.59  thf('10', plain,
% 0.21/0.59      (((((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ sk_B @ sk_A))
% 0.21/0.59         | ~ (v1_relat_1 @ sk_B)))
% 0.21/0.59         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.21/0.59      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.59  thf(t60_relat_1, axiom,
% 0.21/0.59    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.59     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.59  thf('11', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.59      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.59  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('13', plain,
% 0.21/0.59      ((((k1_xboole_0) = (k9_relat_1 @ sk_B @ sk_A)))
% 0.21/0.59         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.21/0.59      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.21/0.59  thf('14', plain,
% 0.21/0.59      ((((k9_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 0.21/0.59         <= (~ (((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.21/0.59      inference('split', [status(esa)], ['0'])).
% 0.21/0.59  thf('15', plain,
% 0.21/0.59      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.59         <= (~ (((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) & 
% 0.21/0.59             ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.59  thf('16', plain,
% 0.21/0.59      ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.21/0.59       ~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.21/0.59      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.59  thf('17', plain, (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.21/0.59      inference('sat_resolution*', [status(thm)], ['2', '16'])).
% 0.21/0.59  thf('18', plain, (~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.21/0.59      inference('simpl_trail', [status(thm)], ['1', '17'])).
% 0.21/0.59  thf('19', plain,
% 0.21/0.59      ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.21/0.59         <= ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.21/0.59      inference('split', [status(esa)], ['3'])).
% 0.21/0.59  thf('20', plain,
% 0.21/0.59      ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.21/0.59       ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.21/0.59      inference('split', [status(esa)], ['3'])).
% 0.21/0.59  thf('21', plain, ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.21/0.59      inference('sat_resolution*', [status(thm)], ['2', '16', '20'])).
% 0.21/0.59  thf('22', plain, (((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.21/0.59      inference('simpl_trail', [status(thm)], ['19', '21'])).
% 0.21/0.59  thf(dt_k7_relat_1, axiom,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.21/0.59  thf('23', plain,
% 0.21/0.59      (![X2 : $i, X3 : $i]:
% 0.21/0.59         (~ (v1_relat_1 @ X2) | (v1_relat_1 @ (k7_relat_1 @ X2 @ X3)))),
% 0.21/0.59      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.21/0.59  thf('24', plain,
% 0.21/0.59      (![X5 : $i, X6 : $i]:
% 0.21/0.59         (((k2_relat_1 @ (k7_relat_1 @ X5 @ X6)) = (k9_relat_1 @ X5 @ X6))
% 0.21/0.59          | ~ (v1_relat_1 @ X5))),
% 0.21/0.59      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.59  thf(fc9_relat_1, axiom,
% 0.21/0.59    (![A:$i]:
% 0.21/0.59     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.21/0.59       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.21/0.59  thf('25', plain,
% 0.21/0.59      (![X4 : $i]:
% 0.21/0.59         (~ (v1_xboole_0 @ (k2_relat_1 @ X4))
% 0.21/0.59          | ~ (v1_relat_1 @ X4)
% 0.21/0.59          | (v1_xboole_0 @ X4))),
% 0.21/0.59      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.21/0.59  thf('26', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         (~ (v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 0.21/0.59          | ~ (v1_relat_1 @ X1)
% 0.21/0.59          | (v1_xboole_0 @ (k7_relat_1 @ X1 @ X0))
% 0.21/0.59          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.59  thf('27', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         (~ (v1_relat_1 @ X1)
% 0.21/0.59          | (v1_xboole_0 @ (k7_relat_1 @ X1 @ X0))
% 0.21/0.59          | ~ (v1_relat_1 @ X1)
% 0.21/0.59          | ~ (v1_xboole_0 @ (k9_relat_1 @ X1 @ X0)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['23', '26'])).
% 0.21/0.59  thf('28', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         (~ (v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 0.21/0.59          | (v1_xboole_0 @ (k7_relat_1 @ X1 @ X0))
% 0.21/0.59          | ~ (v1_relat_1 @ X1))),
% 0.21/0.59      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.59  thf('29', plain,
% 0.21/0.59      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.59        | ~ (v1_relat_1 @ sk_B)
% 0.21/0.59        | (v1_xboole_0 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['22', '28'])).
% 0.21/0.59  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.59  thf('30', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.59      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.59  thf('31', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('32', plain, ((v1_xboole_0 @ (k7_relat_1 @ sk_B @ sk_A))),
% 0.21/0.59      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.21/0.59  thf('33', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.59      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.59  thf(t8_boole, axiom,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.21/0.59  thf('34', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 0.21/0.59      inference('cnf', [status(esa)], [t8_boole])).
% 0.21/0.59  thf('35', plain,
% 0.21/0.59      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.59      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.59  thf('36', plain,
% 0.21/0.59      (![X7 : $i, X8 : $i]:
% 0.21/0.59         (((k7_relat_1 @ X7 @ X8) != (k1_xboole_0))
% 0.21/0.59          | (r1_xboole_0 @ (k1_relat_1 @ X7) @ X8)
% 0.21/0.59          | ~ (v1_relat_1 @ X7))),
% 0.21/0.59      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.21/0.59  thf('37', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.59         (((k7_relat_1 @ X2 @ X1) != (X0))
% 0.21/0.59          | ~ (v1_xboole_0 @ X0)
% 0.21/0.59          | ~ (v1_relat_1 @ X2)
% 0.21/0.59          | (r1_xboole_0 @ (k1_relat_1 @ X2) @ X1))),
% 0.21/0.59      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.59  thf('38', plain,
% 0.21/0.59      (![X1 : $i, X2 : $i]:
% 0.21/0.59         ((r1_xboole_0 @ (k1_relat_1 @ X2) @ X1)
% 0.21/0.59          | ~ (v1_relat_1 @ X2)
% 0.21/0.59          | ~ (v1_xboole_0 @ (k7_relat_1 @ X2 @ X1)))),
% 0.21/0.59      inference('simplify', [status(thm)], ['37'])).
% 0.21/0.59  thf('39', plain,
% 0.21/0.59      ((~ (v1_relat_1 @ sk_B) | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.21/0.59      inference('sup-', [status(thm)], ['32', '38'])).
% 0.21/0.59  thf('40', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('41', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.21/0.59      inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.59  thf('42', plain, ($false), inference('demod', [status(thm)], ['18', '41'])).
% 0.21/0.59  
% 0.21/0.59  % SZS output end Refutation
% 0.21/0.59  
% 0.21/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
