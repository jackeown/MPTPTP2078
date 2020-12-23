%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YIqxraPE6x

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 109 expanded)
%              Number of leaves         :   16 (  38 expanded)
%              Depth                    :   15
%              Number of atoms          :  391 ( 828 expanded)
%              Number of equality atoms :   39 ( 105 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X12 @ X10 @ X11 ) @ ( sk_E @ X12 @ X10 @ X11 ) ) @ X12 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X12 @ X10 @ X11 ) @ ( sk_E @ X12 @ X10 @ X11 ) ) @ X10 )
      | ( X12
        = ( k5_relat_1 @ X11 @ X10 ) )
      | ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('2',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ~ ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('6',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ X7 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('8',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','7'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

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

thf('14',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X12 @ X10 @ X11 ) @ ( sk_E @ X12 @ X10 @ X11 ) ) @ X12 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X12 @ X10 @ X11 ) @ ( sk_F @ X12 @ X10 @ X11 ) ) @ X11 )
      | ( X12
        = ( k5_relat_1 @ X11 @ X10 ) )
      | ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ k1_xboole_0 @ X1 @ X0 ) @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','7'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ k1_xboole_0 @ X1 @ X0 ) @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','7'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('26',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('31',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['29','30'])).

thf('32',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['15','31'])).

thf('33',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    $false ),
    inference(simplify,[status(thm)],['35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YIqxraPE6x
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:51:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.44  % Solved by: fo/fo7.sh
% 0.21/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.44  % done 29 iterations in 0.027s
% 0.21/0.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.44  % SZS output start Refutation
% 0.21/0.44  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.44  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.44  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.21/0.44  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.21/0.44  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.21/0.44  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.44  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.44  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.44  thf(d8_relat_1, axiom,
% 0.21/0.44    (![A:$i]:
% 0.21/0.44     ( ( v1_relat_1 @ A ) =>
% 0.21/0.44       ( ![B:$i]:
% 0.21/0.44         ( ( v1_relat_1 @ B ) =>
% 0.21/0.44           ( ![C:$i]:
% 0.21/0.44             ( ( v1_relat_1 @ C ) =>
% 0.21/0.44               ( ( ( C ) = ( k5_relat_1 @ A @ B ) ) <=>
% 0.21/0.44                 ( ![D:$i,E:$i]:
% 0.21/0.44                   ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 0.21/0.44                     ( ?[F:$i]:
% 0.21/0.44                       ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B ) & 
% 0.21/0.44                         ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.44  thf('0', plain,
% 0.21/0.44      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.44         (~ (v1_relat_1 @ X10)
% 0.21/0.44          | (r2_hidden @ 
% 0.21/0.44             (k4_tarski @ (sk_D_1 @ X12 @ X10 @ X11) @ (sk_E @ X12 @ X10 @ X11)) @ 
% 0.21/0.44             X12)
% 0.21/0.44          | (r2_hidden @ 
% 0.21/0.44             (k4_tarski @ (sk_F @ X12 @ X10 @ X11) @ (sk_E @ X12 @ X10 @ X11)) @ 
% 0.21/0.44             X10)
% 0.21/0.44          | ((X12) = (k5_relat_1 @ X11 @ X10))
% 0.21/0.44          | ~ (v1_relat_1 @ X12)
% 0.21/0.44          | ~ (v1_relat_1 @ X11))),
% 0.21/0.44      inference('cnf', [status(esa)], [d8_relat_1])).
% 0.21/0.44  thf(t113_zfmisc_1, axiom,
% 0.21/0.44    (![A:$i,B:$i]:
% 0.21/0.44     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.44       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.44  thf('1', plain,
% 0.21/0.44      (![X1 : $i, X2 : $i]:
% 0.21/0.44         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.21/0.44      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.44  thf('2', plain,
% 0.21/0.44      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.44      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.44  thf(t152_zfmisc_1, axiom,
% 0.21/0.44    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.21/0.44  thf('3', plain,
% 0.21/0.44      (![X3 : $i, X4 : $i]: ~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ X3 @ X4))),
% 0.21/0.44      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.21/0.44  thf('4', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.44      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.44  thf('5', plain,
% 0.21/0.44      (![X0 : $i, X1 : $i]:
% 0.21/0.44         (~ (v1_relat_1 @ X0)
% 0.21/0.44          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.44          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ X1))
% 0.21/0.44          | (r2_hidden @ 
% 0.21/0.44             (k4_tarski @ (sk_F @ k1_xboole_0 @ X1 @ X0) @ 
% 0.21/0.44              (sk_E @ k1_xboole_0 @ X1 @ X0)) @ 
% 0.21/0.44             X1)
% 0.21/0.44          | ~ (v1_relat_1 @ X1))),
% 0.21/0.44      inference('sup-', [status(thm)], ['0', '4'])).
% 0.21/0.44  thf(d1_relat_1, axiom,
% 0.21/0.44    (![A:$i]:
% 0.21/0.44     ( ( v1_relat_1 @ A ) <=>
% 0.21/0.44       ( ![B:$i]:
% 0.21/0.44         ( ~( ( r2_hidden @ B @ A ) & 
% 0.21/0.44              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.21/0.44  thf('6', plain,
% 0.21/0.44      (![X7 : $i]: ((v1_relat_1 @ X7) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 0.21/0.44      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.21/0.44  thf('7', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.44      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.44  thf('8', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.44      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.44  thf('9', plain,
% 0.21/0.44      (![X0 : $i, X1 : $i]:
% 0.21/0.44         (~ (v1_relat_1 @ X0)
% 0.21/0.44          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ X1))
% 0.21/0.44          | (r2_hidden @ 
% 0.21/0.44             (k4_tarski @ (sk_F @ k1_xboole_0 @ X1 @ X0) @ 
% 0.21/0.44              (sk_E @ k1_xboole_0 @ X1 @ X0)) @ 
% 0.21/0.44             X1)
% 0.21/0.44          | ~ (v1_relat_1 @ X1))),
% 0.21/0.44      inference('demod', [status(thm)], ['5', '8'])).
% 0.21/0.44  thf('10', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.44      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.44  thf('11', plain,
% 0.21/0.44      (![X0 : $i]:
% 0.21/0.44         (~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.44          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.21/0.44          | ~ (v1_relat_1 @ X0))),
% 0.21/0.44      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.44  thf('12', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.44      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.44  thf('13', plain,
% 0.21/0.44      (![X0 : $i]:
% 0.21/0.44         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.21/0.44          | ~ (v1_relat_1 @ X0))),
% 0.21/0.44      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.44  thf(t62_relat_1, conjecture,
% 0.21/0.44    (![A:$i]:
% 0.21/0.44     ( ( v1_relat_1 @ A ) =>
% 0.21/0.44       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.21/0.44         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.44    (~( ![A:$i]:
% 0.21/0.44        ( ( v1_relat_1 @ A ) =>
% 0.21/0.44          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.21/0.44            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.21/0.44    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.21/0.44  thf('14', plain,
% 0.21/0.44      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.21/0.44        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf('15', plain,
% 0.21/0.44      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.44         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.44      inference('split', [status(esa)], ['14'])).
% 0.21/0.44  thf('16', plain,
% 0.21/0.44      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.44         (~ (v1_relat_1 @ X10)
% 0.21/0.44          | (r2_hidden @ 
% 0.21/0.44             (k4_tarski @ (sk_D_1 @ X12 @ X10 @ X11) @ (sk_E @ X12 @ X10 @ X11)) @ 
% 0.21/0.44             X12)
% 0.21/0.44          | (r2_hidden @ 
% 0.21/0.44             (k4_tarski @ (sk_D_1 @ X12 @ X10 @ X11) @ (sk_F @ X12 @ X10 @ X11)) @ 
% 0.21/0.44             X11)
% 0.21/0.44          | ((X12) = (k5_relat_1 @ X11 @ X10))
% 0.21/0.44          | ~ (v1_relat_1 @ X12)
% 0.21/0.44          | ~ (v1_relat_1 @ X11))),
% 0.21/0.44      inference('cnf', [status(esa)], [d8_relat_1])).
% 0.21/0.44  thf('17', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.44      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.44  thf('18', plain,
% 0.21/0.44      (![X0 : $i, X1 : $i]:
% 0.21/0.44         (~ (v1_relat_1 @ X0)
% 0.21/0.44          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.44          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ X1))
% 0.21/0.44          | (r2_hidden @ 
% 0.21/0.44             (k4_tarski @ (sk_D_1 @ k1_xboole_0 @ X1 @ X0) @ 
% 0.21/0.44              (sk_F @ k1_xboole_0 @ X1 @ X0)) @ 
% 0.21/0.44             X0)
% 0.21/0.44          | ~ (v1_relat_1 @ X1))),
% 0.21/0.44      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.44  thf('19', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.44      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.44  thf('20', plain,
% 0.21/0.44      (![X0 : $i, X1 : $i]:
% 0.21/0.44         (~ (v1_relat_1 @ X0)
% 0.21/0.44          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ X1))
% 0.21/0.44          | (r2_hidden @ 
% 0.21/0.44             (k4_tarski @ (sk_D_1 @ k1_xboole_0 @ X1 @ X0) @ 
% 0.21/0.44              (sk_F @ k1_xboole_0 @ X1 @ X0)) @ 
% 0.21/0.44             X0)
% 0.21/0.44          | ~ (v1_relat_1 @ X1))),
% 0.21/0.44      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.44  thf('21', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.44      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.44  thf('22', plain,
% 0.21/0.44      (![X0 : $i]:
% 0.21/0.44         (~ (v1_relat_1 @ X0)
% 0.21/0.44          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.21/0.44          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.44      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.44  thf('23', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.44      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.44  thf('24', plain,
% 0.21/0.44      (![X0 : $i]:
% 0.21/0.44         (~ (v1_relat_1 @ X0)
% 0.21/0.44          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.21/0.44      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.44  thf('25', plain,
% 0.21/0.44      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.21/0.44         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.44      inference('split', [status(esa)], ['14'])).
% 0.21/0.44  thf('26', plain,
% 0.21/0.44      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A)))
% 0.21/0.44         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.44      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.44  thf('27', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf('28', plain,
% 0.21/0.44      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.44         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.44      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.44  thf('29', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.44      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.44  thf('30', plain,
% 0.21/0.44      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.21/0.44       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.44      inference('split', [status(esa)], ['14'])).
% 0.21/0.44  thf('31', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.44      inference('sat_resolution*', [status(thm)], ['29', '30'])).
% 0.21/0.44  thf('32', plain, (((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.44      inference('simpl_trail', [status(thm)], ['15', '31'])).
% 0.21/0.44  thf('33', plain,
% 0.21/0.44      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A))),
% 0.21/0.44      inference('sup-', [status(thm)], ['13', '32'])).
% 0.21/0.44  thf('34', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf('35', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.44      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.44  thf('36', plain, ($false), inference('simplify', [status(thm)], ['35'])).
% 0.21/0.44  
% 0.21/0.44  % SZS output end Refutation
% 0.21/0.44  
% 0.21/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
