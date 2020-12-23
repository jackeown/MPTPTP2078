%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Hg0hHrZQxb

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:33 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   56 (  76 expanded)
%              Number of leaves         :   15 (  29 expanded)
%              Depth                    :   19
%              Number of atoms          :  420 ( 593 expanded)
%              Number of equality atoms :   33 (  54 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

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

thf('1',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X6 @ X4 @ X5 ) @ ( sk_E @ X6 @ X4 @ X5 ) ) @ X6 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X6 @ X4 @ X5 ) @ ( sk_E @ X6 @ X4 @ X5 ) ) @ X4 )
      | ( X6
        = ( k5_relat_1 @ X5 @ X4 ) )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X0 @ X2 @ X1 ) @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X2
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

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

thf('6',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('9',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('10',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X6 @ X4 @ X5 ) @ ( sk_E @ X6 @ X4 @ X5 ) ) @ X6 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X6 @ X4 @ X5 ) @ ( sk_F @ X6 @ X4 @ X5 ) ) @ X5 )
      | ( X6
        = ( k5_relat_1 @ X5 @ X4 ) )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X2 @ X1 ) @ ( sk_F @ X0 @ X2 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( X2
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( X1
        = ( k5_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( X1
        = ( k5_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('21',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('22',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('26',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('28',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['26','27'])).

thf('29',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['7','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','29'])).

thf('31',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('32',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('36',plain,(
    ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','36'])).

thf('38',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['37','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Hg0hHrZQxb
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:00:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.41/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.60  % Solved by: fo/fo7.sh
% 0.41/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.60  % done 114 iterations in 0.149s
% 0.41/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.60  % SZS output start Refutation
% 0.41/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.60  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.41/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.60  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.41/0.60  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.41/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.60  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.41/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.60  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.41/0.60  thf(cc1_relat_1, axiom,
% 0.41/0.60    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.41/0.60  thf('0', plain, (![X3 : $i]: ((v1_relat_1 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.41/0.60      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.41/0.60  thf(d8_relat_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( v1_relat_1 @ A ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( v1_relat_1 @ B ) =>
% 0.41/0.60           ( ![C:$i]:
% 0.41/0.60             ( ( v1_relat_1 @ C ) =>
% 0.41/0.60               ( ( ( C ) = ( k5_relat_1 @ A @ B ) ) <=>
% 0.41/0.60                 ( ![D:$i,E:$i]:
% 0.41/0.60                   ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 0.41/0.60                     ( ?[F:$i]:
% 0.41/0.60                       ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B ) & 
% 0.41/0.60                         ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.60  thf('1', plain,
% 0.41/0.60      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.41/0.60         (~ (v1_relat_1 @ X4)
% 0.41/0.60          | (r2_hidden @ 
% 0.41/0.60             (k4_tarski @ (sk_D @ X6 @ X4 @ X5) @ (sk_E @ X6 @ X4 @ X5)) @ X6)
% 0.41/0.60          | (r2_hidden @ 
% 0.41/0.60             (k4_tarski @ (sk_F @ X6 @ X4 @ X5) @ (sk_E @ X6 @ X4 @ X5)) @ X4)
% 0.41/0.60          | ((X6) = (k5_relat_1 @ X5 @ X4))
% 0.41/0.60          | ~ (v1_relat_1 @ X6)
% 0.41/0.60          | ~ (v1_relat_1 @ X5))),
% 0.41/0.60      inference('cnf', [status(esa)], [d8_relat_1])).
% 0.41/0.60  thf(d1_xboole_0, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.41/0.60  thf('2', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.41/0.60      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.60  thf('3', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.60         (~ (v1_relat_1 @ X1)
% 0.41/0.60          | ~ (v1_relat_1 @ X0)
% 0.41/0.60          | ((X0) = (k5_relat_1 @ X1 @ X2))
% 0.41/0.60          | (r2_hidden @ 
% 0.41/0.60             (k4_tarski @ (sk_F @ X0 @ X2 @ X1) @ (sk_E @ X0 @ X2 @ X1)) @ X2)
% 0.41/0.60          | ~ (v1_relat_1 @ X2)
% 0.41/0.60          | ~ (v1_xboole_0 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.41/0.60  thf('4', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.41/0.60      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.60  thf('5', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.60         (~ (v1_xboole_0 @ X2)
% 0.41/0.60          | ~ (v1_relat_1 @ X0)
% 0.41/0.60          | ((X2) = (k5_relat_1 @ X1 @ X0))
% 0.41/0.60          | ~ (v1_relat_1 @ X2)
% 0.41/0.60          | ~ (v1_relat_1 @ X1)
% 0.41/0.60          | ~ (v1_xboole_0 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['3', '4'])).
% 0.41/0.60  thf(t62_relat_1, conjecture,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( v1_relat_1 @ A ) =>
% 0.41/0.60       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.41/0.60         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.41/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.60    (~( ![A:$i]:
% 0.41/0.60        ( ( v1_relat_1 @ A ) =>
% 0.41/0.60          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.41/0.60            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.41/0.60    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.41/0.60  thf('6', plain,
% 0.41/0.60      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.41/0.60        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('7', plain,
% 0.41/0.60      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.41/0.60         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.41/0.60      inference('split', [status(esa)], ['6'])).
% 0.41/0.60  thf('8', plain, (![X3 : $i]: ((v1_relat_1 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.41/0.60      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.41/0.60  thf('9', plain, (![X3 : $i]: ((v1_relat_1 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.41/0.60      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.41/0.60  thf('10', plain,
% 0.41/0.60      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.41/0.60         (~ (v1_relat_1 @ X4)
% 0.41/0.60          | (r2_hidden @ 
% 0.41/0.60             (k4_tarski @ (sk_D @ X6 @ X4 @ X5) @ (sk_E @ X6 @ X4 @ X5)) @ X6)
% 0.41/0.60          | (r2_hidden @ 
% 0.41/0.60             (k4_tarski @ (sk_D @ X6 @ X4 @ X5) @ (sk_F @ X6 @ X4 @ X5)) @ X5)
% 0.41/0.60          | ((X6) = (k5_relat_1 @ X5 @ X4))
% 0.41/0.60          | ~ (v1_relat_1 @ X6)
% 0.41/0.60          | ~ (v1_relat_1 @ X5))),
% 0.41/0.60      inference('cnf', [status(esa)], [d8_relat_1])).
% 0.41/0.60  thf('11', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.41/0.60      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.60  thf('12', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.60         (~ (v1_relat_1 @ X1)
% 0.41/0.60          | ~ (v1_relat_1 @ X0)
% 0.41/0.60          | ((X0) = (k5_relat_1 @ X1 @ X2))
% 0.41/0.60          | (r2_hidden @ 
% 0.41/0.60             (k4_tarski @ (sk_D @ X0 @ X2 @ X1) @ (sk_F @ X0 @ X2 @ X1)) @ X1)
% 0.41/0.60          | ~ (v1_relat_1 @ X2)
% 0.41/0.60          | ~ (v1_xboole_0 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['10', '11'])).
% 0.41/0.60  thf('13', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.41/0.60      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.60  thf('14', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.60         (~ (v1_xboole_0 @ X2)
% 0.41/0.60          | ~ (v1_relat_1 @ X1)
% 0.41/0.60          | ((X2) = (k5_relat_1 @ X0 @ X1))
% 0.41/0.60          | ~ (v1_relat_1 @ X2)
% 0.41/0.60          | ~ (v1_relat_1 @ X0)
% 0.41/0.60          | ~ (v1_xboole_0 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['12', '13'])).
% 0.41/0.60  thf('15', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.60         (~ (v1_xboole_0 @ X0)
% 0.41/0.60          | ~ (v1_xboole_0 @ X0)
% 0.41/0.60          | ~ (v1_relat_1 @ X1)
% 0.41/0.60          | ((X1) = (k5_relat_1 @ X0 @ X2))
% 0.41/0.60          | ~ (v1_relat_1 @ X2)
% 0.41/0.60          | ~ (v1_xboole_0 @ X1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['9', '14'])).
% 0.41/0.60  thf('16', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.60         (~ (v1_xboole_0 @ X1)
% 0.41/0.60          | ~ (v1_relat_1 @ X2)
% 0.41/0.60          | ((X1) = (k5_relat_1 @ X0 @ X2))
% 0.41/0.60          | ~ (v1_relat_1 @ X1)
% 0.41/0.60          | ~ (v1_xboole_0 @ X0))),
% 0.41/0.60      inference('simplify', [status(thm)], ['15'])).
% 0.41/0.60  thf('17', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.60         (~ (v1_xboole_0 @ X0)
% 0.41/0.60          | ~ (v1_xboole_0 @ X1)
% 0.41/0.60          | ((X0) = (k5_relat_1 @ X1 @ X2))
% 0.41/0.60          | ~ (v1_relat_1 @ X2)
% 0.41/0.60          | ~ (v1_xboole_0 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['8', '16'])).
% 0.41/0.60  thf('18', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.60         (~ (v1_relat_1 @ X2)
% 0.41/0.60          | ((X0) = (k5_relat_1 @ X1 @ X2))
% 0.41/0.60          | ~ (v1_xboole_0 @ X1)
% 0.41/0.60          | ~ (v1_xboole_0 @ X0))),
% 0.41/0.60      inference('simplify', [status(thm)], ['17'])).
% 0.41/0.60  thf('19', plain,
% 0.41/0.60      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.41/0.60         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.41/0.60      inference('split', [status(esa)], ['6'])).
% 0.41/0.60  thf('20', plain,
% 0.41/0.60      ((![X0 : $i]:
% 0.41/0.60          (((X0) != (k1_xboole_0))
% 0.41/0.60           | ~ (v1_xboole_0 @ X0)
% 0.41/0.60           | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.41/0.60           | ~ (v1_relat_1 @ sk_A)))
% 0.41/0.60         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['18', '19'])).
% 0.41/0.60  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.41/0.60  thf('21', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.60      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.41/0.60  thf('22', plain, ((v1_relat_1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('23', plain,
% 0.41/0.60      ((![X0 : $i]: (((X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.41/0.60         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.41/0.60      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.41/0.60  thf('24', plain,
% 0.41/0.60      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.41/0.60         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.41/0.60      inference('simplify', [status(thm)], ['23'])).
% 0.41/0.60  thf('25', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.60      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.41/0.60  thf('26', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.41/0.60      inference('simplify_reflect+', [status(thm)], ['24', '25'])).
% 0.41/0.60  thf('27', plain,
% 0.41/0.60      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.41/0.60       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.41/0.60      inference('split', [status(esa)], ['6'])).
% 0.41/0.60  thf('28', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.41/0.60      inference('sat_resolution*', [status(thm)], ['26', '27'])).
% 0.41/0.60  thf('29', plain, (((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.41/0.60      inference('simpl_trail', [status(thm)], ['7', '28'])).
% 0.41/0.60  thf('30', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (((X0) != (k1_xboole_0))
% 0.41/0.60          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.41/0.60          | ~ (v1_relat_1 @ sk_A)
% 0.41/0.60          | ~ (v1_relat_1 @ X0)
% 0.41/0.60          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.41/0.60          | ~ (v1_xboole_0 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['5', '29'])).
% 0.41/0.60  thf('31', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.60      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.41/0.60  thf('32', plain, ((v1_relat_1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('33', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (((X0) != (k1_xboole_0))
% 0.41/0.60          | ~ (v1_relat_1 @ X0)
% 0.41/0.60          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.41/0.60          | ~ (v1_xboole_0 @ X0))),
% 0.41/0.60      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.41/0.60  thf('34', plain,
% 0.41/0.60      ((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.41/0.60      inference('simplify', [status(thm)], ['33'])).
% 0.41/0.60  thf('35', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.60      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.41/0.60  thf('36', plain, (~ (v1_relat_1 @ k1_xboole_0)),
% 0.41/0.60      inference('simplify_reflect+', [status(thm)], ['34', '35'])).
% 0.41/0.60  thf('37', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.60      inference('sup-', [status(thm)], ['0', '36'])).
% 0.41/0.60  thf('38', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.60      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.41/0.60  thf('39', plain, ($false), inference('demod', [status(thm)], ['37', '38'])).
% 0.41/0.60  
% 0.41/0.60  % SZS output end Refutation
% 0.41/0.60  
% 0.44/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
