%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gmc8XntHv9

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:50 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   35 (  35 expanded)
%              Number of leaves         :   19 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :  158 ( 158 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X38: $i] :
      ( ( v1_relat_1 @ X38 )
      | ~ ( v1_xboole_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
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

thf('3',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( r2_hidden @ X41 @ ( k10_relat_1 @ X42 @ X40 ) )
      | ( r2_hidden @ ( k4_tarski @ X41 @ ( sk_D @ X42 @ X40 @ X41 ) ) @ X42 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k10_relat_1 @ X1 @ X0 ) ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('6',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X32 != X34 )
      | ~ ( r2_hidden @ X32 @ ( k4_xboole_0 @ X33 @ ( k1_tarski @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('7',plain,(
    ! [X33: $i,X34: $i] :
      ~ ( r2_hidden @ X34 @ ( k4_xboole_0 @ X33 @ ( k1_tarski @ X34 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','9'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('11',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','12'])).

thf('14',plain,(
    $false ),
    inference(simplify,[status(thm)],['13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gmc8XntHv9
% 0.14/0.37  % Computer   : n018.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 16:42:57 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.22/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.55  % Solved by: fo/fo7.sh
% 0.22/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.55  % done 127 iterations in 0.069s
% 0.22/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.55  % SZS output start Refutation
% 0.22/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.55  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.22/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.55  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.22/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.55  thf(t172_relat_1, conjecture,
% 0.22/0.55    (![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.55    (~( ![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.22/0.55    inference('cnf.neg', [status(esa)], [t172_relat_1])).
% 0.22/0.55  thf('0', plain, (((k10_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(cc1_relat_1, axiom,
% 0.22/0.55    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.22/0.55  thf('1', plain, (![X38 : $i]: ((v1_relat_1 @ X38) | ~ (v1_xboole_0 @ X38))),
% 0.22/0.55      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.22/0.55  thf(t7_xboole_0, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.55          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.22/0.55  thf('2', plain,
% 0.22/0.55      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.22/0.55      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.22/0.55  thf(t166_relat_1, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ( v1_relat_1 @ C ) =>
% 0.22/0.55       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.22/0.55         ( ?[D:$i]:
% 0.22/0.55           ( ( r2_hidden @ D @ B ) & 
% 0.22/0.55             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.22/0.55             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.22/0.55  thf('3', plain,
% 0.22/0.55      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.22/0.55         (~ (r2_hidden @ X41 @ (k10_relat_1 @ X42 @ X40))
% 0.22/0.55          | (r2_hidden @ (k4_tarski @ X41 @ (sk_D @ X42 @ X40 @ X41)) @ X42)
% 0.22/0.55          | ~ (v1_relat_1 @ X42))),
% 0.22/0.55      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.22/0.55  thf('4', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (((k10_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.22/0.55          | ~ (v1_relat_1 @ X1)
% 0.22/0.55          | (r2_hidden @ 
% 0.22/0.55             (k4_tarski @ (sk_B @ (k10_relat_1 @ X1 @ X0)) @ 
% 0.22/0.55              (sk_D @ X1 @ X0 @ (sk_B @ (k10_relat_1 @ X1 @ X0)))) @ 
% 0.22/0.55             X1))),
% 0.22/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.55  thf(t4_boole, axiom,
% 0.22/0.55    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.55  thf('5', plain,
% 0.22/0.55      (![X3 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.22/0.55      inference('cnf', [status(esa)], [t4_boole])).
% 0.22/0.55  thf(t64_zfmisc_1, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.22/0.55       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.22/0.55  thf('6', plain,
% 0.22/0.55      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.22/0.55         (((X32) != (X34))
% 0.22/0.55          | ~ (r2_hidden @ X32 @ (k4_xboole_0 @ X33 @ (k1_tarski @ X34))))),
% 0.22/0.55      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.22/0.55  thf('7', plain,
% 0.22/0.55      (![X33 : $i, X34 : $i]:
% 0.22/0.55         ~ (r2_hidden @ X34 @ (k4_xboole_0 @ X33 @ (k1_tarski @ X34)))),
% 0.22/0.55      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.55  thf('8', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.22/0.55      inference('sup-', [status(thm)], ['5', '7'])).
% 0.22/0.55  thf('9', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.55          | ((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['4', '8'])).
% 0.22/0.55  thf('10', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.22/0.55          | ((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['1', '9'])).
% 0.22/0.55  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.22/0.55  thf('11', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.55  thf('12', plain,
% 0.22/0.55      (![X0 : $i]: ((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.22/0.55      inference('demod', [status(thm)], ['10', '11'])).
% 0.22/0.55  thf('13', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.55      inference('demod', [status(thm)], ['0', '12'])).
% 0.22/0.55  thf('14', plain, ($false), inference('simplify', [status(thm)], ['13'])).
% 0.22/0.55  
% 0.22/0.55  % SZS output end Refutation
% 0.22/0.55  
% 0.22/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
