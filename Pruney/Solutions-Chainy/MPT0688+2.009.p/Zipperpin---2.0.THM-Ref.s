%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qHTD43OB3a

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   41 (  50 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :   11
%              Number of atoms          :  313 ( 407 expanded)
%              Number of equality atoms :   23 (  28 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t143_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( ( k10_relat_1 @ B @ ( k1_tarski @ C ) )
                = k1_xboole_0 ) )
       => ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( ( k10_relat_1 @ B @ ( k1_tarski @ C ) )
                  = k1_xboole_0 ) )
         => ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t143_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('2',plain,(
    ! [X9: $i] :
      ( r1_xboole_0 @ X9 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X20 ) @ X21 )
      | ~ ( r2_hidden @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t142_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
      <=> ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) )
         != k1_xboole_0 ) ) ) )).

thf('6',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k10_relat_1 @ X22 @ ( k1_tarski @ X23 ) )
        = k1_xboole_0 )
      | ( r2_hidden @ X23 @ ( k2_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t142_funct_1])).

thf('7',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k1_tarski @ ( sk_D @ X2 @ ( k2_relat_1 @ X0 ) @ X1 ) ) )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k2_relat_1 @ X0 ) @ X1 ) @ X2 )
      | ( X2
        = ( k4_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X24: $i] :
      ( ~ ( r2_hidden @ X24 @ sk_A )
      | ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ X24 ) )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) )
      | ( r2_hidden @ ( sk_D @ X1 @ ( k2_relat_1 @ sk_B ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ ( k2_relat_1 @ sk_B ) @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) )
      | ( r2_hidden @ ( sk_D @ X1 @ ( k2_relat_1 @ sk_B ) @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ ( k2_relat_1 @ sk_B ) @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X1 @ ( k2_relat_1 @ sk_B ) @ X0 ) @ sk_A )
      | ( r2_hidden @ ( sk_D @ X1 @ ( k2_relat_1 @ sk_B ) @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ) )
    | ( k1_xboole_0
      = ( k4_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ) )
    | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','13'])).

thf('15',plain,
    ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k4_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('17',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( ( k4_xboole_0 @ X6 @ X7 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('19',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    $false ),
    inference(demod,[status(thm)],['0','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qHTD43OB3a
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:51:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 100 iterations in 0.068s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.53  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(t143_funct_1, conjecture,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ B ) =>
% 0.21/0.53       ( ( ![C:$i]:
% 0.21/0.53           ( ~( ( r2_hidden @ C @ A ) & 
% 0.21/0.53                ( ( k10_relat_1 @ B @ ( k1_tarski @ C ) ) = ( k1_xboole_0 ) ) ) ) ) =>
% 0.21/0.53         ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i,B:$i]:
% 0.21/0.53        ( ( v1_relat_1 @ B ) =>
% 0.21/0.53          ( ( ![C:$i]:
% 0.21/0.53              ( ~( ( r2_hidden @ C @ A ) & 
% 0.21/0.53                   ( ( k10_relat_1 @ B @ ( k1_tarski @ C ) ) = ( k1_xboole_0 ) ) ) ) ) =>
% 0.21/0.53            ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t143_funct_1])).
% 0.21/0.53  thf('0', plain, (~ (r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(d5_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.21/0.53       ( ![D:$i]:
% 0.21/0.53         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.53           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.21/0.53         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.21/0.53          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.21/0.53          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.21/0.53      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.53  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.21/0.53  thf('2', plain, (![X9 : $i]: (r1_xboole_0 @ X9 @ k1_xboole_0)),
% 0.21/0.53      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.53  thf(l24_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (![X20 : $i, X21 : $i]:
% 0.21/0.53         (~ (r1_xboole_0 @ (k1_tarski @ X20) @ X21) | ~ (r2_hidden @ X20 @ X21))),
% 0.21/0.53      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.21/0.53  thf('4', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.21/0.53          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['1', '4'])).
% 0.21/0.53  thf(t142_funct_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ B ) =>
% 0.21/0.53       ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) <=>
% 0.21/0.53         ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X22 : $i, X23 : $i]:
% 0.21/0.53         (((k10_relat_1 @ X22 @ (k1_tarski @ X23)) = (k1_xboole_0))
% 0.21/0.53          | (r2_hidden @ X23 @ (k2_relat_1 @ X22))
% 0.21/0.53          | ~ (v1_relat_1 @ X22))),
% 0.21/0.53      inference('cnf', [status(esa)], [t142_funct_1])).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.21/0.53         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.21/0.53          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.21/0.53          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.21/0.53      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X0)
% 0.21/0.53          | ((k10_relat_1 @ X0 @ 
% 0.21/0.53              (k1_tarski @ (sk_D @ X2 @ (k2_relat_1 @ X0) @ X1)))
% 0.21/0.53              = (k1_xboole_0))
% 0.21/0.53          | (r2_hidden @ (sk_D @ X2 @ (k2_relat_1 @ X0) @ X1) @ X2)
% 0.21/0.53          | ((X2) = (k4_xboole_0 @ X1 @ (k2_relat_1 @ X0))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (![X24 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X24 @ sk_A)
% 0.21/0.53          | ((k10_relat_1 @ sk_B @ (k1_tarski @ X24)) != (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.53          | ((X1) = (k4_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))
% 0.21/0.53          | (r2_hidden @ (sk_D @ X1 @ (k2_relat_1 @ sk_B) @ X0) @ X1)
% 0.21/0.53          | ~ (v1_relat_1 @ sk_B)
% 0.21/0.53          | ~ (r2_hidden @ (sk_D @ X1 @ (k2_relat_1 @ sk_B) @ X0) @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.53  thf('11', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.53          | ((X1) = (k4_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))
% 0.21/0.53          | (r2_hidden @ (sk_D @ X1 @ (k2_relat_1 @ sk_B) @ X0) @ X1)
% 0.21/0.53          | ~ (r2_hidden @ (sk_D @ X1 @ (k2_relat_1 @ sk_B) @ X0) @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (r2_hidden @ (sk_D @ X1 @ (k2_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.21/0.53          | (r2_hidden @ (sk_D @ X1 @ (k2_relat_1 @ sk_B) @ X0) @ X1)
% 0.21/0.53          | ((X1) = (k4_xboole_0 @ X0 @ (k2_relat_1 @ sk_B))))),
% 0.21/0.53      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      ((((k1_xboole_0) = (k4_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B)))
% 0.21/0.53        | ((k1_xboole_0) = (k4_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B)))
% 0.21/0.53        | (r2_hidden @ (sk_D @ k1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A) @ 
% 0.21/0.53           k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['5', '13'])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (((r2_hidden @ (sk_D @ k1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A) @ 
% 0.21/0.53         k1_xboole_0)
% 0.21/0.53        | ((k1_xboole_0) = (k4_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.21/0.53      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.53  thf('16', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.21/0.53      inference('clc', [status(thm)], ['15', '16'])).
% 0.21/0.53  thf(l32_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      (![X6 : $i, X7 : $i]:
% 0.21/0.53         ((r1_tarski @ X6 @ X7) | ((k4_xboole_0 @ X6 @ X7) != (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.53        | (r1_tarski @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.53  thf('20', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.21/0.53      inference('simplify', [status(thm)], ['19'])).
% 0.21/0.53  thf('21', plain, ($false), inference('demod', [status(thm)], ['0', '20'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
