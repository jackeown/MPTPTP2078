%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kgfu3xxE0U

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:29 EST 2020

% Result     : Theorem 0.16s
% Output     : Refutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   53 (  64 expanded)
%              Number of leaves         :   24 (  31 expanded)
%              Depth                    :   13
%              Number of atoms          :  314 ( 383 expanded)
%              Number of equality atoms :    3 (   4 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v5_funct_1_type,type,(
    v5_funct_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('0',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ X13 )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('1',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ( r2_hidden @ ( sk_B_1 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

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
    ! [X0: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X12: $i] :
      ( ( ( k10_relat_1 @ X12 @ ( k2_relat_1 @ X12 ) )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k10_relat_1 @ X11 @ X9 ) )
      | ( r2_hidden @ ( k4_tarski @ X10 @ ( sk_D_1 @ X11 @ X9 @ X10 ) ) @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_D_1 @ X0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_D_1 @ X0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_relat_1 @ X0 ) ) @ ( sk_D_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( sk_B @ ( k1_relat_1 @ X0 ) ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf(d20_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( v5_funct_1 @ B @ A )
          <=> ! [C: $i] :
                ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
               => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( r2_hidden @ ( sk_C_1 @ X14 @ X15 ) @ ( k1_relat_1 @ X14 ) )
      | ( v5_funct_1 @ X14 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d20_funct_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v5_funct_1 @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v5_funct_1 @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v5_funct_1 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v5_funct_1 @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t174_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( v5_funct_1 @ k1_xboole_0 @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( v5_funct_1 @ k1_xboole_0 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t174_funct_1])).

thf('22',plain,(
    ~ ( v5_funct_1 @ k1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('24',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('25',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['23','24','25','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.10  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kgfu3xxE0U
% 0.10/0.30  % Computer   : n017.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % DateTime   : Tue Dec  1 10:23:46 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.10/0.30  % Running portfolio for 600 s
% 0.10/0.30  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.10/0.30  % Number of cores: 8
% 0.10/0.31  % Python version: Python 3.6.8
% 0.10/0.31  % Running in FO mode
% 0.16/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.16/0.47  % Solved by: fo/fo7.sh
% 0.16/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.16/0.47  % done 52 iterations in 0.049s
% 0.16/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.16/0.47  % SZS output start Refutation
% 0.16/0.47  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.16/0.47  thf(v5_funct_1_type, type, v5_funct_1: $i > $i > $o).
% 0.16/0.47  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.16/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.16/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.16/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.16/0.47  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.16/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.16/0.47  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.16/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.16/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.16/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.16/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.16/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.16/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.16/0.47  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.16/0.47  thf(cc1_funct_1, axiom,
% 0.16/0.47    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 0.16/0.47  thf('0', plain, (![X13 : $i]: ((v1_funct_1 @ X13) | ~ (v1_xboole_0 @ X13))),
% 0.16/0.47      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.16/0.47  thf(d1_relat_1, axiom,
% 0.16/0.47    (![A:$i]:
% 0.16/0.47     ( ( v1_relat_1 @ A ) <=>
% 0.16/0.47       ( ![B:$i]:
% 0.16/0.47         ( ~( ( r2_hidden @ B @ A ) & 
% 0.16/0.47              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.16/0.47  thf('1', plain,
% 0.16/0.47      (![X5 : $i]: ((v1_relat_1 @ X5) | (r2_hidden @ (sk_B_1 @ X5) @ X5))),
% 0.16/0.47      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.16/0.47  thf(d1_xboole_0, axiom,
% 0.16/0.47    (![A:$i]:
% 0.16/0.47     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.16/0.47  thf('2', plain,
% 0.16/0.47      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.16/0.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.16/0.47  thf('3', plain, (![X0 : $i]: ((v1_relat_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.16/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.16/0.47  thf('4', plain,
% 0.16/0.47      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.16/0.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.16/0.47  thf(t169_relat_1, axiom,
% 0.16/0.47    (![A:$i]:
% 0.16/0.47     ( ( v1_relat_1 @ A ) =>
% 0.16/0.47       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.16/0.47  thf('5', plain,
% 0.16/0.47      (![X12 : $i]:
% 0.16/0.47         (((k10_relat_1 @ X12 @ (k2_relat_1 @ X12)) = (k1_relat_1 @ X12))
% 0.16/0.47          | ~ (v1_relat_1 @ X12))),
% 0.16/0.47      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.16/0.47  thf(t166_relat_1, axiom,
% 0.16/0.47    (![A:$i,B:$i,C:$i]:
% 0.16/0.47     ( ( v1_relat_1 @ C ) =>
% 0.16/0.47       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.16/0.47         ( ?[D:$i]:
% 0.16/0.47           ( ( r2_hidden @ D @ B ) & 
% 0.16/0.47             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.16/0.47             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.16/0.47  thf('6', plain,
% 0.16/0.47      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.16/0.47         (~ (r2_hidden @ X10 @ (k10_relat_1 @ X11 @ X9))
% 0.16/0.47          | (r2_hidden @ (k4_tarski @ X10 @ (sk_D_1 @ X11 @ X9 @ X10)) @ X11)
% 0.16/0.47          | ~ (v1_relat_1 @ X11))),
% 0.16/0.47      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.16/0.47  thf('7', plain,
% 0.16/0.47      (![X0 : $i, X1 : $i]:
% 0.16/0.47         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.16/0.47          | ~ (v1_relat_1 @ X0)
% 0.16/0.47          | ~ (v1_relat_1 @ X0)
% 0.16/0.47          | (r2_hidden @ 
% 0.16/0.47             (k4_tarski @ X1 @ (sk_D_1 @ X0 @ (k2_relat_1 @ X0) @ X1)) @ X0))),
% 0.16/0.47      inference('sup-', [status(thm)], ['5', '6'])).
% 0.16/0.47  thf('8', plain,
% 0.16/0.47      (![X0 : $i, X1 : $i]:
% 0.16/0.47         ((r2_hidden @ 
% 0.16/0.47           (k4_tarski @ X1 @ (sk_D_1 @ X0 @ (k2_relat_1 @ X0) @ X1)) @ X0)
% 0.16/0.47          | ~ (v1_relat_1 @ X0)
% 0.16/0.47          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.16/0.47      inference('simplify', [status(thm)], ['7'])).
% 0.16/0.47  thf('9', plain,
% 0.16/0.47      (![X0 : $i]:
% 0.16/0.47         ((v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.16/0.47          | ~ (v1_relat_1 @ X0)
% 0.16/0.47          | (r2_hidden @ 
% 0.16/0.47             (k4_tarski @ (sk_B @ (k1_relat_1 @ X0)) @ 
% 0.16/0.47              (sk_D_1 @ X0 @ (k2_relat_1 @ X0) @ (sk_B @ (k1_relat_1 @ X0)))) @ 
% 0.16/0.47             X0))),
% 0.16/0.47      inference('sup-', [status(thm)], ['4', '8'])).
% 0.16/0.47  thf('10', plain,
% 0.16/0.47      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.16/0.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.16/0.47  thf('11', plain,
% 0.16/0.47      (![X0 : $i]:
% 0.16/0.47         (~ (v1_relat_1 @ X0)
% 0.16/0.47          | (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.16/0.47          | ~ (v1_xboole_0 @ X0))),
% 0.16/0.47      inference('sup-', [status(thm)], ['9', '10'])).
% 0.16/0.47  thf('12', plain, (![X0 : $i]: ((v1_relat_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.16/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.16/0.47  thf('13', plain,
% 0.16/0.47      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.16/0.47      inference('clc', [status(thm)], ['11', '12'])).
% 0.16/0.47  thf(d20_funct_1, axiom,
% 0.16/0.47    (![A:$i]:
% 0.16/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.16/0.47       ( ![B:$i]:
% 0.16/0.47         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.16/0.47           ( ( v5_funct_1 @ B @ A ) <=>
% 0.16/0.47             ( ![C:$i]:
% 0.16/0.47               ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.16/0.47                 ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.16/0.47  thf('14', plain,
% 0.16/0.47      (![X14 : $i, X15 : $i]:
% 0.16/0.47         (~ (v1_relat_1 @ X14)
% 0.16/0.47          | ~ (v1_funct_1 @ X14)
% 0.16/0.47          | (r2_hidden @ (sk_C_1 @ X14 @ X15) @ (k1_relat_1 @ X14))
% 0.16/0.47          | (v5_funct_1 @ X14 @ X15)
% 0.16/0.47          | ~ (v1_funct_1 @ X15)
% 0.16/0.47          | ~ (v1_relat_1 @ X15))),
% 0.16/0.47      inference('cnf', [status(esa)], [d20_funct_1])).
% 0.16/0.47  thf('15', plain,
% 0.16/0.47      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.16/0.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.16/0.47  thf('16', plain,
% 0.16/0.47      (![X0 : $i, X1 : $i]:
% 0.16/0.47         (~ (v1_relat_1 @ X1)
% 0.16/0.47          | ~ (v1_funct_1 @ X1)
% 0.16/0.47          | (v5_funct_1 @ X0 @ X1)
% 0.16/0.47          | ~ (v1_funct_1 @ X0)
% 0.16/0.47          | ~ (v1_relat_1 @ X0)
% 0.16/0.47          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.16/0.47      inference('sup-', [status(thm)], ['14', '15'])).
% 0.16/0.47  thf('17', plain,
% 0.16/0.47      (![X0 : $i, X1 : $i]:
% 0.16/0.47         (~ (v1_xboole_0 @ X0)
% 0.16/0.47          | ~ (v1_relat_1 @ X0)
% 0.16/0.47          | ~ (v1_funct_1 @ X0)
% 0.16/0.47          | (v5_funct_1 @ X0 @ X1)
% 0.16/0.47          | ~ (v1_funct_1 @ X1)
% 0.16/0.47          | ~ (v1_relat_1 @ X1))),
% 0.16/0.47      inference('sup-', [status(thm)], ['13', '16'])).
% 0.16/0.47  thf('18', plain,
% 0.16/0.47      (![X0 : $i, X1 : $i]:
% 0.16/0.47         (~ (v1_xboole_0 @ X0)
% 0.16/0.47          | ~ (v1_relat_1 @ X1)
% 0.16/0.47          | ~ (v1_funct_1 @ X1)
% 0.16/0.47          | (v5_funct_1 @ X0 @ X1)
% 0.16/0.47          | ~ (v1_funct_1 @ X0)
% 0.16/0.47          | ~ (v1_xboole_0 @ X0))),
% 0.16/0.47      inference('sup-', [status(thm)], ['3', '17'])).
% 0.16/0.47  thf('19', plain,
% 0.16/0.47      (![X0 : $i, X1 : $i]:
% 0.16/0.47         (~ (v1_funct_1 @ X0)
% 0.16/0.47          | (v5_funct_1 @ X0 @ X1)
% 0.16/0.47          | ~ (v1_funct_1 @ X1)
% 0.16/0.47          | ~ (v1_relat_1 @ X1)
% 0.16/0.47          | ~ (v1_xboole_0 @ X0))),
% 0.16/0.47      inference('simplify', [status(thm)], ['18'])).
% 0.16/0.47  thf('20', plain,
% 0.16/0.47      (![X0 : $i, X1 : $i]:
% 0.16/0.47         (~ (v1_xboole_0 @ X0)
% 0.16/0.47          | ~ (v1_xboole_0 @ X0)
% 0.16/0.47          | ~ (v1_relat_1 @ X1)
% 0.16/0.47          | ~ (v1_funct_1 @ X1)
% 0.16/0.47          | (v5_funct_1 @ X0 @ X1))),
% 0.16/0.47      inference('sup-', [status(thm)], ['0', '19'])).
% 0.16/0.47  thf('21', plain,
% 0.16/0.47      (![X0 : $i, X1 : $i]:
% 0.16/0.47         ((v5_funct_1 @ X0 @ X1)
% 0.16/0.47          | ~ (v1_funct_1 @ X1)
% 0.16/0.47          | ~ (v1_relat_1 @ X1)
% 0.16/0.47          | ~ (v1_xboole_0 @ X0))),
% 0.16/0.47      inference('simplify', [status(thm)], ['20'])).
% 0.16/0.47  thf(t174_funct_1, conjecture,
% 0.16/0.47    (![A:$i]:
% 0.16/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.16/0.47       ( v5_funct_1 @ k1_xboole_0 @ A ) ))).
% 0.16/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.16/0.47    (~( ![A:$i]:
% 0.16/0.47        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.16/0.47          ( v5_funct_1 @ k1_xboole_0 @ A ) ) )),
% 0.16/0.47    inference('cnf.neg', [status(esa)], [t174_funct_1])).
% 0.16/0.47  thf('22', plain, (~ (v5_funct_1 @ k1_xboole_0 @ sk_A)),
% 0.16/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.47  thf('23', plain,
% 0.16/0.47      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.16/0.47        | ~ (v1_relat_1 @ sk_A)
% 0.16/0.47        | ~ (v1_funct_1 @ sk_A))),
% 0.16/0.47      inference('sup-', [status(thm)], ['21', '22'])).
% 0.16/0.47  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.16/0.47  thf('24', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.16/0.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.16/0.47  thf('25', plain, ((v1_relat_1 @ sk_A)),
% 0.16/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.47  thf('26', plain, ((v1_funct_1 @ sk_A)),
% 0.16/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.47  thf('27', plain, ($false),
% 0.16/0.47      inference('demod', [status(thm)], ['23', '24', '25', '26'])).
% 0.16/0.47  
% 0.16/0.47  % SZS output end Refutation
% 0.16/0.47  
% 0.16/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
