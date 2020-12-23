%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5IF15yonll

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:04 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   44 (  52 expanded)
%              Number of leaves         :   16 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :  316 ( 421 expanded)
%              Number of equality atoms :   48 (  70 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t66_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = k1_xboole_0 )
        & ( A != k1_xboole_0 )
        & ( A
         != ( k1_tarski @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
            = k1_xboole_0 )
          & ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_zfmisc_1])).

thf('0',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('1',plain,(
    ! [X53: $i,X54: $i] :
      ( ( X53 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X54 @ X53 ) @ X53 )
      | ( X53
        = ( k1_tarski @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('3',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k1_tarski @ X1 ) )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ sk_A ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_A ) @ ( k1_tarski @ sk_B ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('6',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ sk_A ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_A ) @ ( k1_tarski @ sk_B ) )
      | ( sk_A
        = ( k1_tarski @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('8',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('14',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['7','16'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('18',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ( X21 = X18 )
      | ( X20
       != ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('19',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21 = X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C_1 @ X0 @ sk_A )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X53: $i,X54: $i] :
      ( ( X53 = k1_xboole_0 )
      | ( ( sk_C_1 @ X54 @ X53 )
       != X54 )
      | ( X53
        = ( k1_tarski @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( sk_B != X0 )
      | ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['23','24','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5IF15yonll
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:19:39 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.58  % Solved by: fo/fo7.sh
% 0.37/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.58  % done 155 iterations in 0.118s
% 0.37/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.58  % SZS output start Refutation
% 0.37/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.58  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.37/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.58  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.58  thf(t66_zfmisc_1, conjecture,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.37/0.58          ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ))).
% 0.37/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.58    (~( ![A:$i,B:$i]:
% 0.37/0.58        ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.37/0.58             ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ) )),
% 0.37/0.58    inference('cnf.neg', [status(esa)], [t66_zfmisc_1])).
% 0.37/0.58  thf('0', plain,
% 0.37/0.58      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(t41_zfmisc_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.37/0.58          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 0.37/0.58  thf('1', plain,
% 0.37/0.58      (![X53 : $i, X54 : $i]:
% 0.37/0.58         (((X53) = (k1_xboole_0))
% 0.37/0.58          | (r2_hidden @ (sk_C_1 @ X54 @ X53) @ X53)
% 0.37/0.58          | ((X53) = (k1_tarski @ X54)))),
% 0.37/0.58      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.37/0.58  thf(d5_xboole_0, axiom,
% 0.37/0.58    (![A:$i,B:$i,C:$i]:
% 0.37/0.58     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.37/0.58       ( ![D:$i]:
% 0.37/0.58         ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.58           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.37/0.58  thf('2', plain,
% 0.37/0.58      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X2 @ X3)
% 0.37/0.58          | (r2_hidden @ X2 @ X4)
% 0.37/0.58          | (r2_hidden @ X2 @ X5)
% 0.37/0.58          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.37/0.58      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.37/0.58  thf('3', plain,
% 0.37/0.58      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.58         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 0.37/0.58          | (r2_hidden @ X2 @ X4)
% 0.37/0.58          | ~ (r2_hidden @ X2 @ X3))),
% 0.37/0.58      inference('simplify', [status(thm)], ['2'])).
% 0.37/0.58  thf('4', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.58         (((X0) = (k1_tarski @ X1))
% 0.37/0.58          | ((X0) = (k1_xboole_0))
% 0.37/0.58          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X2)
% 0.37/0.58          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X2)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['1', '3'])).
% 0.37/0.58  thf('5', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         ((r2_hidden @ (sk_C_1 @ X0 @ sk_A) @ k1_xboole_0)
% 0.37/0.58          | (r2_hidden @ (sk_C_1 @ X0 @ sk_A) @ (k1_tarski @ sk_B))
% 0.37/0.58          | ((sk_A) = (k1_xboole_0))
% 0.37/0.58          | ((sk_A) = (k1_tarski @ X0)))),
% 0.37/0.58      inference('sup+', [status(thm)], ['0', '4'])).
% 0.37/0.58  thf('6', plain, (((sk_A) != (k1_xboole_0))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('7', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         ((r2_hidden @ (sk_C_1 @ X0 @ sk_A) @ k1_xboole_0)
% 0.37/0.58          | (r2_hidden @ (sk_C_1 @ X0 @ sk_A) @ (k1_tarski @ sk_B))
% 0.37/0.58          | ((sk_A) = (k1_tarski @ X0)))),
% 0.37/0.58      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.37/0.58  thf(t2_boole, axiom,
% 0.37/0.58    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.37/0.58  thf('8', plain,
% 0.37/0.58      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.58      inference('cnf', [status(esa)], [t2_boole])).
% 0.37/0.58  thf(t100_xboole_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.58  thf('9', plain,
% 0.37/0.58      (![X8 : $i, X9 : $i]:
% 0.37/0.58         ((k4_xboole_0 @ X8 @ X9)
% 0.37/0.58           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.37/0.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.58  thf('10', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.58      inference('sup+', [status(thm)], ['8', '9'])).
% 0.37/0.58  thf(t5_boole, axiom,
% 0.37/0.58    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.58  thf('11', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.37/0.58      inference('cnf', [status(esa)], [t5_boole])).
% 0.37/0.58  thf('12', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.37/0.58      inference('sup+', [status(thm)], ['10', '11'])).
% 0.37/0.58  thf('13', plain,
% 0.37/0.58      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X6 @ X5)
% 0.37/0.58          | ~ (r2_hidden @ X6 @ X4)
% 0.37/0.58          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.37/0.58      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.37/0.58  thf('14', plain,
% 0.37/0.58      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X6 @ X4)
% 0.37/0.58          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.37/0.58      inference('simplify', [status(thm)], ['13'])).
% 0.37/0.58  thf('15', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['12', '14'])).
% 0.37/0.58  thf('16', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.37/0.58      inference('condensation', [status(thm)], ['15'])).
% 0.37/0.58  thf('17', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (((sk_A) = (k1_tarski @ X0))
% 0.37/0.58          | (r2_hidden @ (sk_C_1 @ X0 @ sk_A) @ (k1_tarski @ sk_B)))),
% 0.37/0.58      inference('clc', [status(thm)], ['7', '16'])).
% 0.37/0.58  thf(d1_tarski, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.37/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.37/0.58  thf('18', plain,
% 0.37/0.58      (![X18 : $i, X20 : $i, X21 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X21 @ X20)
% 0.37/0.58          | ((X21) = (X18))
% 0.37/0.58          | ((X20) != (k1_tarski @ X18)))),
% 0.37/0.58      inference('cnf', [status(esa)], [d1_tarski])).
% 0.37/0.58  thf('19', plain,
% 0.37/0.58      (![X18 : $i, X21 : $i]:
% 0.37/0.58         (((X21) = (X18)) | ~ (r2_hidden @ X21 @ (k1_tarski @ X18)))),
% 0.37/0.58      inference('simplify', [status(thm)], ['18'])).
% 0.37/0.58  thf('20', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (((sk_A) = (k1_tarski @ X0)) | ((sk_C_1 @ X0 @ sk_A) = (sk_B)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['17', '19'])).
% 0.37/0.58  thf('21', plain,
% 0.37/0.58      (![X53 : $i, X54 : $i]:
% 0.37/0.58         (((X53) = (k1_xboole_0))
% 0.37/0.58          | ((sk_C_1 @ X54 @ X53) != (X54))
% 0.37/0.58          | ((X53) = (k1_tarski @ X54)))),
% 0.37/0.58      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.37/0.58  thf('22', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (((sk_B) != (X0))
% 0.37/0.58          | ((sk_A) = (k1_tarski @ X0))
% 0.37/0.58          | ((sk_A) = (k1_tarski @ X0))
% 0.37/0.58          | ((sk_A) = (k1_xboole_0)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['20', '21'])).
% 0.37/0.58  thf('23', plain,
% 0.37/0.58      ((((sk_A) = (k1_xboole_0)) | ((sk_A) = (k1_tarski @ sk_B)))),
% 0.37/0.58      inference('simplify', [status(thm)], ['22'])).
% 0.37/0.58  thf('24', plain, (((sk_A) != (k1_tarski @ sk_B))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('25', plain, (((sk_A) != (k1_xboole_0))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('26', plain, ($false),
% 0.37/0.58      inference('simplify_reflect-', [status(thm)], ['23', '24', '25'])).
% 0.37/0.58  
% 0.37/0.58  % SZS output end Refutation
% 0.37/0.58  
% 0.37/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
