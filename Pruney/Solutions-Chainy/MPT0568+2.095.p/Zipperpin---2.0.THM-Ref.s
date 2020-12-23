%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PIc6D397z5

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:00 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   35 (  35 expanded)
%              Number of leaves         :   19 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :  155 ( 155 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t172_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k10_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t172_relat_1])).

thf('0',plain,(
    ( k10_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('2',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( r2_hidden @ X41 @ ( k10_relat_1 @ X42 @ X40 ) )
      | ( r2_hidden @ ( k4_tarski @ X41 @ ( sk_D @ X42 @ X40 @ X41 ) ) @ X42 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k10_relat_1 @ X1 @ X0 ) ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('5',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X32 != X34 )
      | ~ ( r2_hidden @ X32 @ ( k4_xboole_0 @ X33 @ ( k1_tarski @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('6',plain,(
    ! [X33: $i,X34: $i] :
      ~ ( r2_hidden @ X34 @ ( k4_xboole_0 @ X33 @ ( k1_tarski @ X34 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('9',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('10',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('11',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','12'])).

thf('14',plain,(
    $false ),
    inference(simplify,[status(thm)],['13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PIc6D397z5
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:52:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 145 iterations in 0.093s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.54  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.54  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.54  thf(t172_relat_1, conjecture,
% 0.20/0.54    (![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t172_relat_1])).
% 0.20/0.54  thf('0', plain, (((k10_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t7_xboole_0, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.54          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.20/0.54      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.54  thf(t166_relat_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ C ) =>
% 0.20/0.54       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.20/0.54         ( ?[D:$i]:
% 0.20/0.54           ( ( r2_hidden @ D @ B ) & 
% 0.20/0.54             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.20/0.54             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X41 @ (k10_relat_1 @ X42 @ X40))
% 0.20/0.54          | (r2_hidden @ (k4_tarski @ X41 @ (sk_D @ X42 @ X40 @ X41)) @ X42)
% 0.20/0.54          | ~ (v1_relat_1 @ X42))),
% 0.20/0.54      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((k10_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.20/0.54          | ~ (v1_relat_1 @ X1)
% 0.20/0.54          | (r2_hidden @ 
% 0.20/0.54             (k4_tarski @ (sk_B @ (k10_relat_1 @ X1 @ X0)) @ 
% 0.20/0.54              (sk_D @ X1 @ X0 @ (sk_B @ (k10_relat_1 @ X1 @ X0)))) @ 
% 0.20/0.54             X1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.54  thf(t4_boole, axiom,
% 0.20/0.54    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      (![X3 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [t4_boole])).
% 0.20/0.54  thf(t64_zfmisc_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.20/0.54       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.54         (((X32) != (X34))
% 0.20/0.54          | ~ (r2_hidden @ X32 @ (k4_xboole_0 @ X33 @ (k1_tarski @ X34))))),
% 0.20/0.54      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      (![X33 : $i, X34 : $i]:
% 0.20/0.54         ~ (r2_hidden @ X34 @ (k4_xboole_0 @ X33 @ (k1_tarski @ X34)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.54  thf('7', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.54      inference('sup-', [status(thm)], ['4', '6'])).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.54          | ((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['3', '7'])).
% 0.20/0.54  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.20/0.54  thf('9', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.20/0.54  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.20/0.54  thf('10', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 0.20/0.54      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.54  thf('11', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.54      inference('sup+', [status(thm)], ['9', '10'])).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (![X0 : $i]: ((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['8', '11'])).
% 0.20/0.54  thf('13', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['0', '12'])).
% 0.20/0.54  thf('14', plain, ($false), inference('simplify', [status(thm)], ['13'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
