%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bm8xVfXygQ

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:43 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 126 expanded)
%              Number of leaves         :   18 (  47 expanded)
%              Depth                    :   15
%              Number of atoms          :  403 ( 924 expanded)
%              Number of equality atoms :   35 (  73 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(d8_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( C
                  = ( k5_relat_1 @ A @ B ) )
              <=> ! [D: $i,E: $i] :
                    ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
                  <=> ? [F: $i] :
                        ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B )
                        & ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X13 @ X11 @ X12 ) @ ( sk_E @ X13 @ X11 @ X12 ) ) @ X13 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X13 @ X11 @ X12 ) @ ( sk_E @ X13 @ X11 @ X12 ) ) @ X11 )
      | ( X13
        = ( k5_relat_1 @ X12 @ X11 ) )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('4',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('5',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('7',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ X8 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('8',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('9',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t62_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
          = k1_xboole_0 )
        & ( ( k5_relat_1 @ A @ k1_xboole_0 )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
            = k1_xboole_0 )
          & ( ( k5_relat_1 @ A @ k1_xboole_0 )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_relat_1])).

thf('15',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X13 @ X11 @ X12 ) @ ( sk_E @ X13 @ X11 @ X12 ) ) @ X13 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X13 @ X11 @ X12 ) @ ( sk_F @ X13 @ X11 @ X12 ) ) @ X12 )
      | ( X13
        = ( k5_relat_1 @ X12 @ X11 ) )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('18',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ k1_xboole_0 @ X1 @ X0 ) @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ k1_xboole_0 @ X1 @ X0 ) @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('27',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('32',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['30','31'])).

thf('33',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['16','32'])).

thf('34',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    $false ),
    inference(simplify,[status(thm)],['36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bm8xVfXygQ
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:09:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.60/0.83  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.60/0.83  % Solved by: fo/fo7.sh
% 0.60/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.83  % done 506 iterations in 0.376s
% 0.60/0.83  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.60/0.83  % SZS output start Refutation
% 0.60/0.83  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.60/0.83  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.60/0.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.60/0.83  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.60/0.83  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.60/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.83  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.60/0.83  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.60/0.83  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.60/0.83  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.60/0.83  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.60/0.83  thf(sk_B_type, type, sk_B: $i > $i).
% 0.60/0.83  thf(d8_relat_1, axiom,
% 0.60/0.83    (![A:$i]:
% 0.60/0.83     ( ( v1_relat_1 @ A ) =>
% 0.60/0.83       ( ![B:$i]:
% 0.60/0.83         ( ( v1_relat_1 @ B ) =>
% 0.60/0.83           ( ![C:$i]:
% 0.60/0.83             ( ( v1_relat_1 @ C ) =>
% 0.60/0.83               ( ( ( C ) = ( k5_relat_1 @ A @ B ) ) <=>
% 0.60/0.83                 ( ![D:$i,E:$i]:
% 0.60/0.83                   ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 0.60/0.83                     ( ?[F:$i]:
% 0.60/0.83                       ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B ) & 
% 0.60/0.83                         ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.60/0.83  thf('0', plain,
% 0.60/0.83      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.60/0.83         (~ (v1_relat_1 @ X11)
% 0.60/0.83          | (r2_hidden @ 
% 0.60/0.83             (k4_tarski @ (sk_D_1 @ X13 @ X11 @ X12) @ (sk_E @ X13 @ X11 @ X12)) @ 
% 0.60/0.83             X13)
% 0.60/0.83          | (r2_hidden @ 
% 0.60/0.83             (k4_tarski @ (sk_F @ X13 @ X11 @ X12) @ (sk_E @ X13 @ X11 @ X12)) @ 
% 0.60/0.83             X11)
% 0.60/0.83          | ((X13) = (k5_relat_1 @ X12 @ X11))
% 0.60/0.83          | ~ (v1_relat_1 @ X13)
% 0.60/0.83          | ~ (v1_relat_1 @ X12))),
% 0.60/0.83      inference('cnf', [status(esa)], [d8_relat_1])).
% 0.60/0.83  thf(t2_boole, axiom,
% 0.60/0.83    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.60/0.83  thf('1', plain,
% 0.60/0.83      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.60/0.83      inference('cnf', [status(esa)], [t2_boole])).
% 0.60/0.83  thf(t4_xboole_0, axiom,
% 0.60/0.83    (![A:$i,B:$i]:
% 0.60/0.83     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.60/0.83            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.60/0.83       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.60/0.83            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.60/0.83  thf('2', plain,
% 0.60/0.83      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.60/0.83         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.60/0.83          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.60/0.83      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.60/0.83  thf('3', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i]:
% 0.60/0.83         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.60/0.83      inference('sup-', [status(thm)], ['1', '2'])).
% 0.60/0.83  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.60/0.83  thf('4', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.60/0.83      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.60/0.83  thf('5', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.60/0.83      inference('demod', [status(thm)], ['3', '4'])).
% 0.60/0.83  thf('6', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i]:
% 0.60/0.83         (~ (v1_relat_1 @ X0)
% 0.60/0.83          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.60/0.83          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ X1))
% 0.60/0.83          | (r2_hidden @ 
% 0.60/0.83             (k4_tarski @ (sk_F @ k1_xboole_0 @ X1 @ X0) @ 
% 0.60/0.83              (sk_E @ k1_xboole_0 @ X1 @ X0)) @ 
% 0.60/0.83             X1)
% 0.60/0.83          | ~ (v1_relat_1 @ X1))),
% 0.60/0.83      inference('sup-', [status(thm)], ['0', '5'])).
% 0.60/0.83  thf(d1_relat_1, axiom,
% 0.60/0.83    (![A:$i]:
% 0.60/0.83     ( ( v1_relat_1 @ A ) <=>
% 0.60/0.83       ( ![B:$i]:
% 0.60/0.83         ( ~( ( r2_hidden @ B @ A ) & 
% 0.60/0.83              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.60/0.83  thf('7', plain,
% 0.60/0.83      (![X8 : $i]: ((v1_relat_1 @ X8) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.60/0.83      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.60/0.83  thf('8', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.60/0.83      inference('demod', [status(thm)], ['3', '4'])).
% 0.60/0.83  thf('9', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.60/0.83      inference('sup-', [status(thm)], ['7', '8'])).
% 0.60/0.83  thf('10', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i]:
% 0.60/0.83         (~ (v1_relat_1 @ X0)
% 0.60/0.83          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ X1))
% 0.60/0.83          | (r2_hidden @ 
% 0.60/0.83             (k4_tarski @ (sk_F @ k1_xboole_0 @ X1 @ X0) @ 
% 0.60/0.83              (sk_E @ k1_xboole_0 @ X1 @ X0)) @ 
% 0.60/0.83             X1)
% 0.60/0.83          | ~ (v1_relat_1 @ X1))),
% 0.60/0.83      inference('demod', [status(thm)], ['6', '9'])).
% 0.60/0.83  thf('11', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.60/0.83      inference('demod', [status(thm)], ['3', '4'])).
% 0.60/0.83  thf('12', plain,
% 0.60/0.83      (![X0 : $i]:
% 0.60/0.83         (~ (v1_relat_1 @ k1_xboole_0)
% 0.60/0.83          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.60/0.83          | ~ (v1_relat_1 @ X0))),
% 0.60/0.83      inference('sup-', [status(thm)], ['10', '11'])).
% 0.60/0.83  thf('13', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.60/0.83      inference('sup-', [status(thm)], ['7', '8'])).
% 0.60/0.83  thf('14', plain,
% 0.60/0.83      (![X0 : $i]:
% 0.60/0.83         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.60/0.83          | ~ (v1_relat_1 @ X0))),
% 0.60/0.83      inference('demod', [status(thm)], ['12', '13'])).
% 0.60/0.83  thf(t62_relat_1, conjecture,
% 0.60/0.83    (![A:$i]:
% 0.60/0.83     ( ( v1_relat_1 @ A ) =>
% 0.60/0.83       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.60/0.83         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.60/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.83    (~( ![A:$i]:
% 0.60/0.83        ( ( v1_relat_1 @ A ) =>
% 0.60/0.83          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.60/0.83            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.60/0.83    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.60/0.83  thf('15', plain,
% 0.60/0.83      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.60/0.83        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('16', plain,
% 0.60/0.83      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.60/0.83         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.60/0.83      inference('split', [status(esa)], ['15'])).
% 0.60/0.83  thf('17', plain,
% 0.60/0.83      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.60/0.83         (~ (v1_relat_1 @ X11)
% 0.60/0.83          | (r2_hidden @ 
% 0.60/0.83             (k4_tarski @ (sk_D_1 @ X13 @ X11 @ X12) @ (sk_E @ X13 @ X11 @ X12)) @ 
% 0.60/0.83             X13)
% 0.60/0.83          | (r2_hidden @ 
% 0.60/0.83             (k4_tarski @ (sk_D_1 @ X13 @ X11 @ X12) @ (sk_F @ X13 @ X11 @ X12)) @ 
% 0.60/0.83             X12)
% 0.60/0.83          | ((X13) = (k5_relat_1 @ X12 @ X11))
% 0.60/0.83          | ~ (v1_relat_1 @ X13)
% 0.60/0.83          | ~ (v1_relat_1 @ X12))),
% 0.60/0.83      inference('cnf', [status(esa)], [d8_relat_1])).
% 0.60/0.83  thf('18', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.60/0.83      inference('demod', [status(thm)], ['3', '4'])).
% 0.60/0.83  thf('19', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i]:
% 0.60/0.83         (~ (v1_relat_1 @ X0)
% 0.60/0.83          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.60/0.83          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ X1))
% 0.60/0.83          | (r2_hidden @ 
% 0.60/0.83             (k4_tarski @ (sk_D_1 @ k1_xboole_0 @ X1 @ X0) @ 
% 0.60/0.83              (sk_F @ k1_xboole_0 @ X1 @ X0)) @ 
% 0.60/0.83             X0)
% 0.60/0.83          | ~ (v1_relat_1 @ X1))),
% 0.60/0.83      inference('sup-', [status(thm)], ['17', '18'])).
% 0.60/0.83  thf('20', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.60/0.83      inference('sup-', [status(thm)], ['7', '8'])).
% 0.60/0.83  thf('21', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i]:
% 0.60/0.83         (~ (v1_relat_1 @ X0)
% 0.60/0.83          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ X1))
% 0.60/0.83          | (r2_hidden @ 
% 0.60/0.83             (k4_tarski @ (sk_D_1 @ k1_xboole_0 @ X1 @ X0) @ 
% 0.60/0.83              (sk_F @ k1_xboole_0 @ X1 @ X0)) @ 
% 0.60/0.83             X0)
% 0.60/0.83          | ~ (v1_relat_1 @ X1))),
% 0.60/0.83      inference('demod', [status(thm)], ['19', '20'])).
% 0.60/0.83  thf('22', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.60/0.83      inference('demod', [status(thm)], ['3', '4'])).
% 0.60/0.83  thf('23', plain,
% 0.60/0.83      (![X0 : $i]:
% 0.60/0.83         (~ (v1_relat_1 @ X0)
% 0.60/0.83          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.60/0.83          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.60/0.83      inference('sup-', [status(thm)], ['21', '22'])).
% 0.60/0.83  thf('24', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.60/0.83      inference('sup-', [status(thm)], ['7', '8'])).
% 0.60/0.83  thf('25', plain,
% 0.60/0.83      (![X0 : $i]:
% 0.60/0.83         (~ (v1_relat_1 @ X0)
% 0.60/0.83          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.60/0.83      inference('demod', [status(thm)], ['23', '24'])).
% 0.60/0.83  thf('26', plain,
% 0.60/0.83      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.60/0.83         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.60/0.83      inference('split', [status(esa)], ['15'])).
% 0.60/0.83  thf('27', plain,
% 0.60/0.83      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A)))
% 0.60/0.83         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.60/0.83      inference('sup-', [status(thm)], ['25', '26'])).
% 0.60/0.83  thf('28', plain, ((v1_relat_1 @ sk_A)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('29', plain,
% 0.60/0.83      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.60/0.83         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.60/0.83      inference('demod', [status(thm)], ['27', '28'])).
% 0.60/0.83  thf('30', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.60/0.83      inference('simplify', [status(thm)], ['29'])).
% 0.60/0.83  thf('31', plain,
% 0.60/0.83      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.60/0.83       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.60/0.83      inference('split', [status(esa)], ['15'])).
% 0.60/0.83  thf('32', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.60/0.83      inference('sat_resolution*', [status(thm)], ['30', '31'])).
% 0.60/0.83  thf('33', plain, (((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.60/0.83      inference('simpl_trail', [status(thm)], ['16', '32'])).
% 0.60/0.83  thf('34', plain,
% 0.60/0.83      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A))),
% 0.60/0.83      inference('sup-', [status(thm)], ['14', '33'])).
% 0.60/0.83  thf('35', plain, ((v1_relat_1 @ sk_A)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('36', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.60/0.83      inference('demod', [status(thm)], ['34', '35'])).
% 0.60/0.83  thf('37', plain, ($false), inference('simplify', [status(thm)], ['36'])).
% 0.60/0.83  
% 0.60/0.83  % SZS output end Refutation
% 0.60/0.83  
% 0.60/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
