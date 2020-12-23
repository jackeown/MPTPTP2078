%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rhnD9LXgAd

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:00 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   39 (  63 expanded)
%              Number of leaves         :   19 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :  215 ( 443 expanded)
%              Number of equality atoms :   27 (  61 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(d10_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( B
          = ( k6_relat_1 @ A ) )
      <=> ! [C: $i,D: $i] :
            ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
          <=> ( ( r2_hidden @ C @ A )
              & ( C = D ) ) ) ) ) )).

thf('0',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X18 @ X19 ) @ ( sk_D @ X18 @ X19 ) ) @ X18 )
      | ( r2_hidden @ ( sk_C @ X18 @ X19 ) @ X19 )
      | ( X18
        = ( k6_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d10_relat_1])).

thf(t75_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k2_tarski @ B @ C ) )
        = k1_xboole_0 )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ( ( k4_xboole_0 @ X16 @ ( k2_tarski @ X14 @ X17 ) )
        = k1_xboole_0 )
      | ( X16 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t75_zfmisc_1])).

thf('2',plain,(
    ! [X14: $i,X17: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ X14 @ X17 ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t77_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_enumset1 @ A @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t77_enumset1])).

thf(t82_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_enumset1 @ A @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('4',plain,(
    ! [X2: $i] :
      ( ( k2_enumset1 @ X2 @ X2 @ X2 @ X2 )
      = ( k1_tarski @ X2 ) ) ),
    inference(cnf,[status(esa)],[t82_enumset1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ( ( k4_xboole_0 @ X12 @ ( k1_tarski @ X11 ) )
       != X12 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X0 ) )
       != X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k6_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('11',plain,(
    ! [X25: $i] :
      ( ( v1_relat_1 @ X25 )
      | ( r2_hidden @ ( sk_B @ X25 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('13',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k6_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('16',plain,
    ( k1_xboole_0
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t81_relat_1,conjecture,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf(zf_stmt_0,negated_conjecture,(
    ( k6_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('cnf.neg',[status(esa)],[t81_relat_1])).

thf('17',plain,(
    ( k6_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rhnD9LXgAd
% 0.12/0.32  % Computer   : n003.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.18/0.32  % CPULimit   : 60
% 0.18/0.32  % DateTime   : Tue Dec  1 13:36:57 EST 2020
% 0.18/0.32  % CPUTime    : 
% 0.18/0.32  % Running portfolio for 600 s
% 0.18/0.32  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.18/0.33  % Number of cores: 8
% 0.18/0.33  % Python version: Python 3.6.8
% 0.18/0.33  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 61 iterations in 0.029s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.19/0.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.46  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.46  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.19/0.46  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.19/0.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.46  thf(d10_relat_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( v1_relat_1 @ B ) =>
% 0.19/0.46       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.19/0.46         ( ![C:$i,D:$i]:
% 0.19/0.46           ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.19/0.46             ( ( r2_hidden @ C @ A ) & ( ( C ) = ( D ) ) ) ) ) ) ))).
% 0.19/0.46  thf('0', plain,
% 0.19/0.46      (![X18 : $i, X19 : $i]:
% 0.19/0.46         ((r2_hidden @ (k4_tarski @ (sk_C @ X18 @ X19) @ (sk_D @ X18 @ X19)) @ 
% 0.19/0.46           X18)
% 0.19/0.46          | (r2_hidden @ (sk_C @ X18 @ X19) @ X19)
% 0.19/0.46          | ((X18) = (k6_relat_1 @ X19))
% 0.19/0.46          | ~ (v1_relat_1 @ X18))),
% 0.19/0.46      inference('cnf', [status(esa)], [d10_relat_1])).
% 0.19/0.46  thf(t75_zfmisc_1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( ( k4_xboole_0 @ A @ ( k2_tarski @ B @ C ) ) = ( k1_xboole_0 ) ) <=>
% 0.19/0.46       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.19/0.46            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.19/0.46  thf('1', plain,
% 0.19/0.46      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.19/0.46         (((k4_xboole_0 @ X16 @ (k2_tarski @ X14 @ X17)) = (k1_xboole_0))
% 0.19/0.46          | ((X16) != (k1_xboole_0)))),
% 0.19/0.46      inference('cnf', [status(esa)], [t75_zfmisc_1])).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      (![X14 : $i, X17 : $i]:
% 0.19/0.46         ((k4_xboole_0 @ k1_xboole_0 @ (k2_tarski @ X14 @ X17)) = (k1_xboole_0))),
% 0.19/0.46      inference('simplify', [status(thm)], ['1'])).
% 0.19/0.46  thf(t77_enumset1, axiom,
% 0.19/0.46    (![A:$i,B:$i]: ( ( k2_enumset1 @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.19/0.46  thf('3', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1) = (k2_tarski @ X0 @ X1))),
% 0.19/0.46      inference('cnf', [status(esa)], [t77_enumset1])).
% 0.19/0.46  thf(t82_enumset1, axiom,
% 0.19/0.46    (![A:$i]: ( ( k2_enumset1 @ A @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.46  thf('4', plain,
% 0.19/0.46      (![X2 : $i]: ((k2_enumset1 @ X2 @ X2 @ X2 @ X2) = (k1_tarski @ X2))),
% 0.19/0.46      inference('cnf', [status(esa)], [t82_enumset1])).
% 0.19/0.46  thf('5', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.19/0.46      inference('sup+', [status(thm)], ['3', '4'])).
% 0.19/0.46  thf(t65_zfmisc_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.19/0.46       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.19/0.46  thf('6', plain,
% 0.19/0.46      (![X11 : $i, X12 : $i]:
% 0.19/0.46         (~ (r2_hidden @ X11 @ X12)
% 0.19/0.46          | ((k4_xboole_0 @ X12 @ (k1_tarski @ X11)) != (X12)))),
% 0.19/0.46      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.19/0.46  thf('7', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (((k4_xboole_0 @ X1 @ (k2_tarski @ X0 @ X0)) != (X1))
% 0.19/0.46          | ~ (r2_hidden @ X0 @ X1))),
% 0.19/0.46      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.46  thf('8', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.19/0.46      inference('sup-', [status(thm)], ['2', '7'])).
% 0.19/0.46  thf('9', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.19/0.46      inference('simplify', [status(thm)], ['8'])).
% 0.19/0.46  thf('10', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (~ (v1_relat_1 @ k1_xboole_0)
% 0.19/0.46          | ((k1_xboole_0) = (k6_relat_1 @ X0))
% 0.19/0.46          | (r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ X0))),
% 0.19/0.46      inference('sup-', [status(thm)], ['0', '9'])).
% 0.19/0.46  thf(d1_relat_1, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( v1_relat_1 @ A ) <=>
% 0.19/0.46       ( ![B:$i]:
% 0.19/0.46         ( ~( ( r2_hidden @ B @ A ) & 
% 0.19/0.46              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.19/0.46  thf('11', plain,
% 0.19/0.46      (![X25 : $i]: ((v1_relat_1 @ X25) | (r2_hidden @ (sk_B @ X25) @ X25))),
% 0.19/0.46      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.19/0.46  thf('12', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.19/0.46      inference('simplify', [status(thm)], ['8'])).
% 0.19/0.46  thf('13', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.19/0.46      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.46  thf('14', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (((k1_xboole_0) = (k6_relat_1 @ X0))
% 0.19/0.46          | (r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ X0))),
% 0.19/0.46      inference('demod', [status(thm)], ['10', '13'])).
% 0.19/0.46  thf('15', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.19/0.46      inference('simplify', [status(thm)], ['8'])).
% 0.19/0.46  thf('16', plain, (((k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 0.19/0.46      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.46  thf(t81_relat_1, conjecture,
% 0.19/0.46    (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (( k6_relat_1 @ k1_xboole_0 ) != ( k1_xboole_0 )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t81_relat_1])).
% 0.19/0.46  thf('17', plain, (((k6_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('18', plain, ($false),
% 0.19/0.46      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
