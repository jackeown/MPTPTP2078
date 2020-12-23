%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bik8HOggrF

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   44 (  61 expanded)
%              Number of leaves         :   16 (  24 expanded)
%              Depth                    :   12
%              Number of atoms          :  349 ( 523 expanded)
%              Number of equality atoms :   28 (  42 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('7',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','9'])).

thf(t142_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
      <=> ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) )
         != k1_xboole_0 ) ) ) )).

thf('11',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k10_relat_1 @ X22 @ ( k1_tarski @ X23 ) )
        = k1_xboole_0 )
      | ( r2_hidden @ X23 @ ( k2_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t142_funct_1])).

thf('12',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k1_tarski @ ( sk_D @ X2 @ ( k2_relat_1 @ X0 ) @ X1 ) ) )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k2_relat_1 @ X0 ) @ X1 ) @ X2 )
      | ( X2
        = ( k4_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X24: $i] :
      ( ~ ( r2_hidden @ X24 @ sk_A )
      | ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ X24 ) )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) )
      | ( r2_hidden @ ( sk_D @ X1 @ ( k2_relat_1 @ sk_B ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ ( k2_relat_1 @ sk_B ) @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) )
      | ( r2_hidden @ ( sk_D @ X1 @ ( k2_relat_1 @ sk_B ) @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ ( k2_relat_1 @ sk_B ) @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X1 @ ( k2_relat_1 @ sk_B ) @ X0 ) @ sk_A )
      | ( r2_hidden @ ( sk_D @ X1 @ ( k2_relat_1 @ sk_B ) @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ) )
    | ( k1_xboole_0
      = ( k4_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ) )
    | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('20',plain,
    ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k4_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['8'])).

thf('22',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( ( k4_xboole_0 @ X9 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('24',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    $false ),
    inference(demod,[status(thm)],['0','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bik8HOggrF
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:29:03 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 62 iterations in 0.062s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.52  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.22/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.52  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.52  thf(t143_funct_1, conjecture,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ B ) =>
% 0.22/0.52       ( ( ![C:$i]:
% 0.22/0.52           ( ~( ( r2_hidden @ C @ A ) & 
% 0.22/0.52                ( ( k10_relat_1 @ B @ ( k1_tarski @ C ) ) = ( k1_xboole_0 ) ) ) ) ) =>
% 0.22/0.52         ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i,B:$i]:
% 0.22/0.52        ( ( v1_relat_1 @ B ) =>
% 0.22/0.52          ( ( ![C:$i]:
% 0.22/0.52              ( ~( ( r2_hidden @ C @ A ) & 
% 0.22/0.52                   ( ( k10_relat_1 @ B @ ( k1_tarski @ C ) ) = ( k1_xboole_0 ) ) ) ) ) =>
% 0.22/0.52            ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t143_funct_1])).
% 0.22/0.52  thf('0', plain, (~ (r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(d5_xboole_0, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.22/0.52       ( ![D:$i]:
% 0.22/0.52         ( ( r2_hidden @ D @ C ) <=>
% 0.22/0.52           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.22/0.52         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.22/0.52          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.22/0.52          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.22/0.52      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.22/0.52  thf(d10_xboole_0, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.52  thf('2', plain,
% 0.22/0.52      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 0.22/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.52  thf('3', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.22/0.52      inference('simplify', [status(thm)], ['2'])).
% 0.22/0.52  thf(l32_xboole_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      (![X9 : $i, X11 : $i]:
% 0.22/0.52         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 0.22/0.52      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.22/0.52  thf('5', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.52  thf('6', plain,
% 0.22/0.52      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X4 @ X3)
% 0.22/0.52          | ~ (r2_hidden @ X4 @ X2)
% 0.22/0.52          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.22/0.52      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.22/0.52  thf('7', plain,
% 0.22/0.52      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X4 @ X2)
% 0.22/0.52          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['5', '7'])).
% 0.22/0.52  thf('9', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.22/0.52      inference('condensation', [status(thm)], ['8'])).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.22/0.52          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['1', '9'])).
% 0.22/0.52  thf(t142_funct_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ B ) =>
% 0.22/0.52       ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) <=>
% 0.22/0.52         ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      (![X22 : $i, X23 : $i]:
% 0.22/0.52         (((k10_relat_1 @ X22 @ (k1_tarski @ X23)) = (k1_xboole_0))
% 0.22/0.52          | (r2_hidden @ X23 @ (k2_relat_1 @ X22))
% 0.22/0.52          | ~ (v1_relat_1 @ X22))),
% 0.22/0.52      inference('cnf', [status(esa)], [t142_funct_1])).
% 0.22/0.52  thf('12', plain,
% 0.22/0.52      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.22/0.52         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.22/0.52          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.22/0.52          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.22/0.52      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.52         (~ (v1_relat_1 @ X0)
% 0.22/0.52          | ((k10_relat_1 @ X0 @ 
% 0.22/0.52              (k1_tarski @ (sk_D @ X2 @ (k2_relat_1 @ X0) @ X1)))
% 0.22/0.52              = (k1_xboole_0))
% 0.22/0.52          | (r2_hidden @ (sk_D @ X2 @ (k2_relat_1 @ X0) @ X1) @ X2)
% 0.22/0.52          | ((X2) = (k4_xboole_0 @ X1 @ (k2_relat_1 @ X0))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.52  thf('14', plain,
% 0.22/0.52      (![X24 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X24 @ sk_A)
% 0.22/0.52          | ((k10_relat_1 @ sk_B @ (k1_tarski @ X24)) != (k1_xboole_0)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.52          | ((X1) = (k4_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))
% 0.22/0.52          | (r2_hidden @ (sk_D @ X1 @ (k2_relat_1 @ sk_B) @ X0) @ X1)
% 0.22/0.52          | ~ (v1_relat_1 @ sk_B)
% 0.22/0.52          | ~ (r2_hidden @ (sk_D @ X1 @ (k2_relat_1 @ sk_B) @ X0) @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.52  thf('16', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('17', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.52          | ((X1) = (k4_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))
% 0.22/0.52          | (r2_hidden @ (sk_D @ X1 @ (k2_relat_1 @ sk_B) @ X0) @ X1)
% 0.22/0.52          | ~ (r2_hidden @ (sk_D @ X1 @ (k2_relat_1 @ sk_B) @ X0) @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['15', '16'])).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (r2_hidden @ (sk_D @ X1 @ (k2_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.22/0.52          | (r2_hidden @ (sk_D @ X1 @ (k2_relat_1 @ sk_B) @ X0) @ X1)
% 0.22/0.52          | ((X1) = (k4_xboole_0 @ X0 @ (k2_relat_1 @ sk_B))))),
% 0.22/0.52      inference('simplify', [status(thm)], ['17'])).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      ((((k1_xboole_0) = (k4_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B)))
% 0.22/0.52        | ((k1_xboole_0) = (k4_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B)))
% 0.22/0.52        | (r2_hidden @ (sk_D @ k1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A) @ 
% 0.22/0.52           k1_xboole_0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['10', '18'])).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      (((r2_hidden @ (sk_D @ k1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A) @ 
% 0.22/0.52         k1_xboole_0)
% 0.22/0.52        | ((k1_xboole_0) = (k4_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.22/0.52      inference('simplify', [status(thm)], ['19'])).
% 0.22/0.52  thf('21', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.22/0.52      inference('condensation', [status(thm)], ['8'])).
% 0.22/0.52  thf('22', plain,
% 0.22/0.52      (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.22/0.52      inference('clc', [status(thm)], ['20', '21'])).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      (![X9 : $i, X10 : $i]:
% 0.22/0.52         ((r1_tarski @ X9 @ X10) | ((k4_xboole_0 @ X9 @ X10) != (k1_xboole_0)))),
% 0.22/0.52      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      ((((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.52        | (r1_tarski @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.52  thf('25', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.22/0.52      inference('simplify', [status(thm)], ['24'])).
% 0.22/0.52  thf('26', plain, ($false), inference('demod', [status(thm)], ['0', '25'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
