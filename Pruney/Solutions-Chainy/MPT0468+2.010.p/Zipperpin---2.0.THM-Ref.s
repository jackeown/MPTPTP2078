%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cWNCuiAM2O

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   43 (  49 expanded)
%              Number of leaves         :   20 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :  241 ( 301 expanded)
%              Number of equality atoms :   20 (  26 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t56_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ! [B: $i,C: $i] :
            ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
       => ( A = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ! [B: $i,C: $i] :
              ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
         => ( A = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t56_relat_1])).

thf('0',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(d2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( A = B )
          <=> ! [C: $i,D: $i] :
                ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
              <=> ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) )).

thf('4',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X23 @ X24 ) @ ( sk_D @ X23 @ X24 ) ) @ X24 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X23 @ X24 ) @ ( sk_D @ X23 @ X24 ) ) @ X23 )
      | ( X24 = X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_relat_1])).

thf('5',plain,(
    ! [X30: $i,X31: $i] :
      ~ ( r2_hidden @ ( k4_tarski @ X30 @ X31 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ( sk_A = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_A ) @ ( sk_D @ X0 @ sk_A ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( sk_A = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_A ) @ ( sk_D @ X0 @ sk_A ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t91_enumset1,axiom,(
    ! [A: $i] :
      ( ( k4_enumset1 @ A @ A @ A @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('9',plain,(
    ! [X16: $i] :
      ( ( k4_enumset1 @ X16 @ X16 @ X16 @ X16 @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t91_enumset1])).

thf(t88_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_enumset1 @ A @ A @ A @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_enumset1 @ X14 @ X14 @ X14 @ X14 @ X14 @ X15 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t88_enumset1])).

thf('11',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = k1_xboole_0 ) )).

thf('12',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X17 ) @ ( k2_tarski @ X17 @ X18 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t22_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('14',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( X19 != X21 )
      | ~ ( r2_hidden @ X19 @ ( k4_xboole_0 @ X20 @ ( k1_tarski @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('15',plain,(
    ! [X20: $i,X21: $i] :
      ~ ( r2_hidden @ X21 @ ( k4_xboole_0 @ X20 @ ( k1_tarski @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','16'])).

thf('18',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ~ ( v1_relat_1 @ X0 ) ),
    inference('sup-',[status(thm)],['3','19'])).

thf('21',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cWNCuiAM2O
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:42:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 31 iterations in 0.023s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.51  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.21/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.51  thf(t56_relat_1, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ A ) =>
% 0.21/0.51       ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 0.21/0.51         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( v1_relat_1 @ A ) =>
% 0.21/0.51          ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 0.21/0.51            ( ( A ) = ( k1_xboole_0 ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t56_relat_1])).
% 0.21/0.51  thf('0', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t2_boole, axiom,
% 0.21/0.51    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.51  thf(fc1_relat_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X28 : $i, X29 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X28) | (v1_relat_1 @ (k3_xboole_0 @ X28 @ X29)))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X0 : $i]: ((v1_relat_1 @ k1_xboole_0) | ~ (v1_relat_1 @ X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.51  thf(d2_relat_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( v1_relat_1 @ B ) =>
% 0.21/0.51           ( ( ( A ) = ( B ) ) <=>
% 0.21/0.51             ( ![C:$i,D:$i]:
% 0.21/0.51               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) <=>
% 0.21/0.51                 ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ) ))).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X23 : $i, X24 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X23)
% 0.21/0.51          | (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ (sk_C @ X23 @ X24) @ (sk_D @ X23 @ X24)) @ X24)
% 0.21/0.51          | (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ (sk_C @ X23 @ X24) @ (sk_D @ X23 @ X24)) @ X23)
% 0.21/0.51          | ((X24) = (X23))
% 0.21/0.51          | ~ (v1_relat_1 @ X24))),
% 0.21/0.51      inference('cnf', [status(esa)], [d2_relat_1])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X30 : $i, X31 : $i]: ~ (r2_hidden @ (k4_tarski @ X30 @ X31) @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ sk_A)
% 0.21/0.51          | ((sk_A) = (X0))
% 0.21/0.51          | (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ (sk_C @ X0 @ sk_A) @ (sk_D @ X0 @ sk_A)) @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.51  thf('7', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((sk_A) = (X0))
% 0.21/0.51          | (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ (sk_C @ X0 @ sk_A) @ (sk_D @ X0 @ sk_A)) @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.51  thf(t91_enumset1, axiom,
% 0.21/0.51    (![A:$i]: ( ( k4_enumset1 @ A @ A @ A @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X16 : $i]:
% 0.21/0.51         ((k4_enumset1 @ X16 @ X16 @ X16 @ X16 @ X16 @ X16) = (k1_tarski @ X16))),
% 0.21/0.51      inference('cnf', [status(esa)], [t91_enumset1])).
% 0.21/0.51  thf(t88_enumset1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( k4_enumset1 @ A @ A @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X14 : $i, X15 : $i]:
% 0.21/0.51         ((k4_enumset1 @ X14 @ X14 @ X14 @ X14 @ X14 @ X15)
% 0.21/0.51           = (k2_tarski @ X14 @ X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [t88_enumset1])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.21/0.51      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.51  thf(t22_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.21/0.51       ( k1_xboole_0 ) ))).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X17 : $i, X18 : $i]:
% 0.21/0.51         ((k4_xboole_0 @ (k1_tarski @ X17) @ (k2_tarski @ X17 @ X18))
% 0.21/0.51           = (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [t22_zfmisc_1])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf(t64_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.21/0.51       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.51         (((X19) != (X21))
% 0.21/0.51          | ~ (r2_hidden @ X19 @ (k4_xboole_0 @ X20 @ (k1_tarski @ X21))))),
% 0.21/0.51      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X20 : $i, X21 : $i]:
% 0.21/0.51         ~ (r2_hidden @ X21 @ (k4_xboole_0 @ X20 @ (k1_tarski @ X21)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.51  thf('16', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.51      inference('sup-', [status(thm)], ['13', '15'])).
% 0.21/0.51  thf('17', plain, ((~ (v1_relat_1 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['8', '16'])).
% 0.21/0.51  thf('18', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('19', plain, (~ (v1_relat_1 @ k1_xboole_0)),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.21/0.51  thf('20', plain, (![X0 : $i]: ~ (v1_relat_1 @ X0)),
% 0.21/0.51      inference('sup-', [status(thm)], ['3', '19'])).
% 0.21/0.51  thf('21', plain, ($false), inference('sup-', [status(thm)], ['0', '20'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
