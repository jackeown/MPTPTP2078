%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fpJbppR0Lk

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:07 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   69 (  90 expanded)
%              Number of leaves         :   26 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :  461 ( 679 expanded)
%              Number of equality atoms :   47 (  67 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t95_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( ( k7_relat_1 @ B @ A )
            = k1_xboole_0 )
        <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t95_relat_1])).

thf('0',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X45 @ X46 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X45 ) @ X46 ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('5',plain,
    ( ( ( ( k1_relat_1 @ k1_xboole_0 )
        = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('6',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('7',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('10',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
      = ( k5_xboole_0 @ ( k1_relat_1 @ sk_B ) @ k1_xboole_0 ) )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('12',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
      = ( k1_relat_1 @ sk_B ) )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_xboole_0 @ X8 @ ( k4_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','18'])).

thf('20',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('23',plain,(
    ! [X47: $i,X48: $i] :
      ( ( ( k7_relat_1 @ X48 @ X47 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X47 ) @ X48 ) )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('24',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('26',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('27',plain,(
    ! [X44: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t67_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_xboole_0 @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k5_relat_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf('28',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( v1_relat_1 @ X41 )
      | ( ( k5_relat_1 @ X42 @ X41 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( k2_relat_1 @ X42 ) @ ( k1_relat_1 @ X41 ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t67_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('30',plain,(
    ! [X40: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( ( k7_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['23','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k7_relat_1 @ sk_B @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','21','22','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fpJbppR0Lk
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:59:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 45 iterations in 0.020s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.48  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.22/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(t95_relat_1, conjecture,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( v1_relat_1 @ B ) =>
% 0.22/0.48       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.48         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i,B:$i]:
% 0.22/0.48        ( ( v1_relat_1 @ B ) =>
% 0.22/0.48          ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.48            ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t95_relat_1])).
% 0.22/0.48  thf('0', plain,
% 0.22/0.48      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.22/0.48        | ((k7_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('1', plain,
% 0.22/0.48      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.22/0.48       ~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.22/0.48      inference('split', [status(esa)], ['0'])).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.22/0.48        | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.22/0.48         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.22/0.48      inference('split', [status(esa)], ['2'])).
% 0.22/0.48  thf(t90_relat_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( v1_relat_1 @ B ) =>
% 0.22/0.48       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.22/0.48         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.48  thf('4', plain,
% 0.22/0.48      (![X45 : $i, X46 : $i]:
% 0.22/0.48         (((k1_relat_1 @ (k7_relat_1 @ X45 @ X46))
% 0.22/0.48            = (k3_xboole_0 @ (k1_relat_1 @ X45) @ X46))
% 0.22/0.48          | ~ (v1_relat_1 @ X45))),
% 0.22/0.48      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.22/0.48  thf('5', plain,
% 0.22/0.48      (((((k1_relat_1 @ k1_xboole_0)
% 0.22/0.48           = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.22/0.48         | ~ (v1_relat_1 @ sk_B)))
% 0.22/0.48         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.22/0.48      inference('sup+', [status(thm)], ['3', '4'])).
% 0.22/0.48  thf(t60_relat_1, axiom,
% 0.22/0.48    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.22/0.48     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.48  thf('6', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.48      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.48  thf('7', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('8', plain,
% 0.22/0.48      ((((k1_xboole_0) = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 0.22/0.48         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.22/0.48      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.22/0.48  thf(t100_xboole_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.48  thf('9', plain,
% 0.22/0.48      (![X5 : $i, X6 : $i]:
% 0.22/0.48         ((k4_xboole_0 @ X5 @ X6)
% 0.22/0.48           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.22/0.48      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.48  thf('10', plain,
% 0.22/0.48      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.22/0.48          = (k5_xboole_0 @ (k1_relat_1 @ sk_B) @ k1_xboole_0)))
% 0.22/0.48         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.22/0.48      inference('sup+', [status(thm)], ['8', '9'])).
% 0.22/0.48  thf(t5_boole, axiom,
% 0.22/0.48    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.48  thf('11', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.22/0.48      inference('cnf', [status(esa)], [t5_boole])).
% 0.22/0.48  thf('12', plain,
% 0.22/0.48      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A) = (k1_relat_1 @ sk_B)))
% 0.22/0.48         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.22/0.48      inference('demod', [status(thm)], ['10', '11'])).
% 0.22/0.48  thf(d10_xboole_0, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.48  thf('13', plain,
% 0.22/0.48      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.22/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.48  thf('14', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.22/0.48      inference('simplify', [status(thm)], ['13'])).
% 0.22/0.48  thf(t85_xboole_1, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.22/0.48  thf('15', plain,
% 0.22/0.48      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.48         (~ (r1_tarski @ X8 @ X9)
% 0.22/0.48          | (r1_xboole_0 @ X8 @ (k4_xboole_0 @ X10 @ X9)))),
% 0.22/0.48      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.22/0.48  thf('16', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.48  thf(symmetry_r1_xboole_0, axiom,
% 0.22/0.48    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.22/0.48  thf('17', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.22/0.48      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.22/0.48  thf('18', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.22/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.48  thf('19', plain,
% 0.22/0.48      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.22/0.48         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.22/0.48      inference('sup+', [status(thm)], ['12', '18'])).
% 0.22/0.48  thf('20', plain,
% 0.22/0.48      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.22/0.48         <= (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.22/0.48      inference('split', [status(esa)], ['0'])).
% 0.22/0.48  thf('21', plain,
% 0.22/0.48      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.22/0.48       ~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.48  thf('22', plain,
% 0.22/0.48      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.22/0.48       (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.22/0.48      inference('split', [status(esa)], ['2'])).
% 0.22/0.48  thf(t94_relat_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( v1_relat_1 @ B ) =>
% 0.22/0.48       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.22/0.48  thf('23', plain,
% 0.22/0.48      (![X47 : $i, X48 : $i]:
% 0.22/0.48         (((k7_relat_1 @ X48 @ X47) = (k5_relat_1 @ (k6_relat_1 @ X47) @ X48))
% 0.22/0.48          | ~ (v1_relat_1 @ X48))),
% 0.22/0.48      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.22/0.48  thf('24', plain,
% 0.22/0.48      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.22/0.48         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.22/0.48      inference('split', [status(esa)], ['2'])).
% 0.22/0.48  thf('25', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.22/0.48      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.22/0.48  thf('26', plain,
% 0.22/0.48      (((r1_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.22/0.48         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.48  thf(t71_relat_1, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.22/0.48       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.22/0.48  thf('27', plain, (![X44 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X44)) = (X44))),
% 0.22/0.48      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.48  thf(t67_relat_1, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( v1_relat_1 @ A ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( v1_relat_1 @ B ) =>
% 0.22/0.48           ( ( r1_xboole_0 @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.22/0.48             ( ( k5_relat_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.22/0.48  thf('28', plain,
% 0.22/0.48      (![X41 : $i, X42 : $i]:
% 0.22/0.48         (~ (v1_relat_1 @ X41)
% 0.22/0.48          | ((k5_relat_1 @ X42 @ X41) = (k1_xboole_0))
% 0.22/0.48          | ~ (r1_xboole_0 @ (k2_relat_1 @ X42) @ (k1_relat_1 @ X41))
% 0.22/0.48          | ~ (v1_relat_1 @ X42))),
% 0.22/0.48      inference('cnf', [status(esa)], [t67_relat_1])).
% 0.22/0.48  thf('29', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         (~ (r1_xboole_0 @ X0 @ (k1_relat_1 @ X1))
% 0.22/0.48          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.22/0.48          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k1_xboole_0))
% 0.22/0.48          | ~ (v1_relat_1 @ X1))),
% 0.22/0.48      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.48  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.22/0.48  thf('30', plain, (![X40 : $i]: (v1_relat_1 @ (k6_relat_1 @ X40))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.48  thf('31', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         (~ (r1_xboole_0 @ X0 @ (k1_relat_1 @ X1))
% 0.22/0.48          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k1_xboole_0))
% 0.22/0.48          | ~ (v1_relat_1 @ X1))),
% 0.22/0.48      inference('demod', [status(thm)], ['29', '30'])).
% 0.22/0.48  thf('32', plain,
% 0.22/0.48      (((~ (v1_relat_1 @ sk_B)
% 0.22/0.48         | ((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (k1_xboole_0))))
% 0.22/0.48         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['26', '31'])).
% 0.22/0.48  thf('33', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('34', plain,
% 0.22/0.48      ((((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (k1_xboole_0)))
% 0.22/0.48         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.22/0.48      inference('demod', [status(thm)], ['32', '33'])).
% 0.22/0.48  thf('35', plain,
% 0.22/0.48      (((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)) | ~ (v1_relat_1 @ sk_B)))
% 0.22/0.48         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.22/0.48      inference('sup+', [status(thm)], ['23', '34'])).
% 0.22/0.48  thf('36', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('37', plain,
% 0.22/0.48      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.22/0.48         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.22/0.48      inference('demod', [status(thm)], ['35', '36'])).
% 0.22/0.48  thf('38', plain,
% 0.22/0.48      ((((k7_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 0.22/0.48         <= (~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.22/0.48      inference('split', [status(esa)], ['0'])).
% 0.22/0.48  thf('39', plain,
% 0.22/0.48      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.22/0.48         <= (~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) & 
% 0.22/0.48             ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.48  thf('40', plain,
% 0.22/0.48      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.22/0.48       (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.22/0.48      inference('simplify', [status(thm)], ['39'])).
% 0.22/0.48  thf('41', plain, ($false),
% 0.22/0.48      inference('sat_resolution*', [status(thm)], ['1', '21', '22', '40'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
