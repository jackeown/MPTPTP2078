%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iFb2S3RucX

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 118 expanded)
%              Number of leaves         :   17 (  38 expanded)
%              Depth                    :   20
%              Number of atoms          :  399 ( 966 expanded)
%              Number of equality atoms :   41 (  97 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

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
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X6 ) @ X7 )
      | ( ( k7_relat_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) )
        = ( k9_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
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

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('20',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k9_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('21',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('22',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','16','21'])).

thf('23',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) )
        = ( k9_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t126_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k8_relat_1 @ ( k2_relat_1 @ A ) @ A )
        = A ) ) )).

thf('25',plain,(
    ! [X2: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X2 ) @ X2 )
        = X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t126_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ ( k9_relat_1 @ X1 @ X0 ) @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k8_relat_1 @ ( k9_relat_1 @ X1 @ X0 ) @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k8_relat_1 @ k1_xboole_0 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = ( k7_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['23','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k8_relat_1 @ k1_xboole_0 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = ( k7_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(t137_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k8_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ) )).

thf('32',plain,(
    ! [X3: $i] :
      ( ( ( k8_relat_1 @ k1_xboole_0 @ X3 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t137_relat_1])).

thf('33',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k7_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k7_relat_1 @ X6 @ X7 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('38',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['18','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iFb2S3RucX
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 09:35:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 30 iterations in 0.016s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.48  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.21/0.48  thf(t151_relat_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ B ) =>
% 0.21/0.48       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.48         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i]:
% 0.21/0.48        ( ( v1_relat_1 @ B ) =>
% 0.21/0.48          ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.48            ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t151_relat_1])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.21/0.48        | ((k9_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.21/0.48         <= (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.21/0.48       ~ (((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.21/0.48        | ((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.21/0.48         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.21/0.48      inference('split', [status(esa)], ['3'])).
% 0.21/0.48  thf(t95_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ B ) =>
% 0.21/0.48       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.48         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i]:
% 0.21/0.48         (~ (r1_xboole_0 @ (k1_relat_1 @ X6) @ X7)
% 0.21/0.48          | ((k7_relat_1 @ X6 @ X7) = (k1_xboole_0))
% 0.21/0.48          | ~ (v1_relat_1 @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (((~ (v1_relat_1 @ sk_B) | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))
% 0.21/0.48         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf('7', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.21/0.48         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.21/0.48      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.48  thf(t148_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ B ) =>
% 0.21/0.48       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X4 : $i, X5 : $i]:
% 0.21/0.48         (((k2_relat_1 @ (k7_relat_1 @ X4 @ X5)) = (k9_relat_1 @ X4 @ X5))
% 0.21/0.48          | ~ (v1_relat_1 @ X4))),
% 0.21/0.48      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (((((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ sk_B @ sk_A))
% 0.21/0.48         | ~ (v1_relat_1 @ sk_B)))
% 0.21/0.48         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.21/0.48      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.48  thf(t60_relat_1, axiom,
% 0.21/0.48    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.48     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.48  thf('11', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.48  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      ((((k1_xboole_0) = (k9_relat_1 @ sk_B @ sk_A)))
% 0.21/0.48         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.21/0.48      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      ((((k9_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 0.21/0.48         <= (~ (((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.48         <= (~ (((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) & 
% 0.21/0.48             ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.21/0.48       ~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.21/0.48      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.48  thf('17', plain, (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['2', '16'])).
% 0.21/0.48  thf('18', plain, (~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['1', '17'])).
% 0.21/0.48  thf(dt_k7_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k7_relat_1 @ X0 @ X1)))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.21/0.48         <= ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.21/0.48      inference('split', [status(esa)], ['3'])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.21/0.48       ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.21/0.48      inference('split', [status(esa)], ['3'])).
% 0.21/0.48  thf('22', plain, ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['2', '16', '21'])).
% 0.21/0.48  thf('23', plain, (((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['20', '22'])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      (![X4 : $i, X5 : $i]:
% 0.21/0.48         (((k2_relat_1 @ (k7_relat_1 @ X4 @ X5)) = (k9_relat_1 @ X4 @ X5))
% 0.21/0.48          | ~ (v1_relat_1 @ X4))),
% 0.21/0.48      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.48  thf(t126_relat_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) =>
% 0.21/0.48       ( ( k8_relat_1 @ ( k2_relat_1 @ A ) @ A ) = ( A ) ) ))).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      (![X2 : $i]:
% 0.21/0.48         (((k8_relat_1 @ (k2_relat_1 @ X2) @ X2) = (X2)) | ~ (v1_relat_1 @ X2))),
% 0.21/0.48      inference('cnf', [status(esa)], [t126_relat_1])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (((k8_relat_1 @ (k9_relat_1 @ X1 @ X0) @ (k7_relat_1 @ X1 @ X0))
% 0.21/0.48            = (k7_relat_1 @ X1 @ X0))
% 0.21/0.48          | ~ (v1_relat_1 @ X1)
% 0.21/0.48          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.21/0.48      inference('sup+', [status(thm)], ['24', '25'])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k7_relat_1 @ X0 @ X1)))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X1)
% 0.21/0.48          | ((k8_relat_1 @ (k9_relat_1 @ X1 @ X0) @ (k7_relat_1 @ X1 @ X0))
% 0.21/0.48              = (k7_relat_1 @ X1 @ X0)))),
% 0.21/0.48      inference('clc', [status(thm)], ['26', '27'])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      ((((k8_relat_1 @ k1_xboole_0 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.21/0.48          = (k7_relat_1 @ sk_B @ sk_A))
% 0.21/0.48        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.48      inference('sup+', [status(thm)], ['23', '28'])).
% 0.21/0.48  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('31', plain,
% 0.21/0.48      (((k8_relat_1 @ k1_xboole_0 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.21/0.48         = (k7_relat_1 @ sk_B @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.48  thf(t137_relat_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) =>
% 0.21/0.48       ( ( k8_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.48  thf('32', plain,
% 0.21/0.48      (![X3 : $i]:
% 0.21/0.48         (((k8_relat_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))
% 0.21/0.48          | ~ (v1_relat_1 @ X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [t137_relat_1])).
% 0.21/0.48  thf('33', plain,
% 0.21/0.48      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))
% 0.21/0.48        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.21/0.48      inference('sup+', [status(thm)], ['31', '32'])).
% 0.21/0.48  thf('34', plain,
% 0.21/0.48      ((~ (v1_relat_1 @ sk_B) | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['19', '33'])).
% 0.21/0.48  thf('35', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('36', plain, (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.21/0.48      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.48  thf('37', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i]:
% 0.21/0.48         (((k7_relat_1 @ X6 @ X7) != (k1_xboole_0))
% 0.21/0.48          | (r1_xboole_0 @ (k1_relat_1 @ X6) @ X7)
% 0.21/0.48          | ~ (v1_relat_1 @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.21/0.48  thf('38', plain,
% 0.21/0.48      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.48        | ~ (v1_relat_1 @ sk_B)
% 0.21/0.48        | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.48  thf('39', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('40', plain,
% 0.21/0.48      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.48        | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.48  thf('41', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.21/0.48      inference('simplify', [status(thm)], ['40'])).
% 0.21/0.48  thf('42', plain, ($false), inference('demod', [status(thm)], ['18', '41'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
