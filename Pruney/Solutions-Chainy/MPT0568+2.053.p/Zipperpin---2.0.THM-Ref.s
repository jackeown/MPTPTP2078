%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1LhOIWMzTj

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:54 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   33 (  38 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :  146 ( 180 expanded)
%              Number of equality atoms :   16 (  21 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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

thf(d14_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k10_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ B )
                  & ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_hidden @ ( sk_D @ X25 @ X26 @ X27 ) @ X25 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X25 @ X26 @ X27 ) @ ( sk_E @ X25 @ X26 @ X27 ) ) @ X27 )
      | ( X25
        = ( k10_relat_1 @ X27 @ X26 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('3',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ( ( k4_xboole_0 @ X23 @ ( k1_tarski @ X22 ) )
       != X23 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( X1
        = ( k10_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('7',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('8',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('9',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k10_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('12',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','12'])).

thf('14',plain,(
    $false ),
    inference(simplify,[status(thm)],['13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1LhOIWMzTj
% 0.17/0.37  % Computer   : n019.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.37  % CPULimit   : 60
% 0.17/0.37  % DateTime   : Tue Dec  1 14:06:08 EST 2020
% 0.17/0.37  % CPUTime    : 
% 0.17/0.37  % Running portfolio for 600 s
% 0.17/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.37  % Number of cores: 8
% 0.23/0.37  % Python version: Python 3.6.8
% 0.23/0.38  % Running in FO mode
% 0.23/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.50  % Solved by: fo/fo7.sh
% 0.23/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.50  % done 26 iterations in 0.022s
% 0.23/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.50  % SZS output start Refutation
% 0.23/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.50  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.23/0.50  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.23/0.50  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.23/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.23/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.23/0.50  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.23/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.50  thf(t172_relat_1, conjecture,
% 0.23/0.50    (![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.23/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.50    (~( ![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.23/0.50    inference('cnf.neg', [status(esa)], [t172_relat_1])).
% 0.23/0.50  thf('0', plain, (((k10_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf(d14_relat_1, axiom,
% 0.23/0.50    (![A:$i]:
% 0.23/0.50     ( ( v1_relat_1 @ A ) =>
% 0.23/0.50       ( ![B:$i,C:$i]:
% 0.23/0.50         ( ( ( C ) = ( k10_relat_1 @ A @ B ) ) <=>
% 0.23/0.50           ( ![D:$i]:
% 0.23/0.50             ( ( r2_hidden @ D @ C ) <=>
% 0.23/0.50               ( ?[E:$i]:
% 0.23/0.50                 ( ( r2_hidden @ E @ B ) & 
% 0.23/0.50                   ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) ) ) ))).
% 0.23/0.50  thf('1', plain,
% 0.23/0.50      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.23/0.50         ((r2_hidden @ (sk_D @ X25 @ X26 @ X27) @ X25)
% 0.23/0.50          | (r2_hidden @ 
% 0.23/0.50             (k4_tarski @ (sk_D @ X25 @ X26 @ X27) @ (sk_E @ X25 @ X26 @ X27)) @ 
% 0.23/0.50             X27)
% 0.23/0.50          | ((X25) = (k10_relat_1 @ X27 @ X26))
% 0.23/0.50          | ~ (v1_relat_1 @ X27))),
% 0.23/0.50      inference('cnf', [status(esa)], [d14_relat_1])).
% 0.23/0.50  thf(t4_boole, axiom,
% 0.23/0.50    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.23/0.50  thf('2', plain,
% 0.23/0.50      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.23/0.50      inference('cnf', [status(esa)], [t4_boole])).
% 0.23/0.50  thf(t65_zfmisc_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.23/0.50       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.23/0.50  thf('3', plain,
% 0.23/0.50      (![X22 : $i, X23 : $i]:
% 0.23/0.50         (~ (r2_hidden @ X22 @ X23)
% 0.23/0.50          | ((k4_xboole_0 @ X23 @ (k1_tarski @ X22)) != (X23)))),
% 0.23/0.50      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.23/0.50  thf('4', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         (((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.23/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.23/0.50  thf('5', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.23/0.50      inference('simplify', [status(thm)], ['4'])).
% 0.23/0.50  thf('6', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]:
% 0.23/0.50         (~ (v1_relat_1 @ k1_xboole_0)
% 0.23/0.50          | ((X1) = (k10_relat_1 @ k1_xboole_0 @ X0))
% 0.23/0.50          | (r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1))),
% 0.23/0.50      inference('sup-', [status(thm)], ['1', '5'])).
% 0.23/0.50  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.23/0.50  thf('7', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.50      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.23/0.50  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.23/0.50  thf('8', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.23/0.50      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.23/0.50  thf('9', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.23/0.50      inference('sup+', [status(thm)], ['7', '8'])).
% 0.23/0.50  thf('10', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]:
% 0.23/0.50         (((X1) = (k10_relat_1 @ k1_xboole_0 @ X0))
% 0.23/0.50          | (r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1))),
% 0.23/0.50      inference('demod', [status(thm)], ['6', '9'])).
% 0.23/0.50  thf('11', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.23/0.50      inference('simplify', [status(thm)], ['4'])).
% 0.23/0.50  thf('12', plain,
% 0.23/0.50      (![X0 : $i]: ((k1_xboole_0) = (k10_relat_1 @ k1_xboole_0 @ X0))),
% 0.23/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.23/0.50  thf('13', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.23/0.50      inference('demod', [status(thm)], ['0', '12'])).
% 0.23/0.50  thf('14', plain, ($false), inference('simplify', [status(thm)], ['13'])).
% 0.23/0.50  
% 0.23/0.50  % SZS output end Refutation
% 0.23/0.50  
% 0.23/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
