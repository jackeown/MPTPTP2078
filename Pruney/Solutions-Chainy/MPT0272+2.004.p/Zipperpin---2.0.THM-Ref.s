%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2mVfQKzRoq

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:26 EST 2020

% Result     : Theorem 19.10s
% Output     : Refutation 19.10s
% Verified   : 
% Statistics : Number of formulae       :   54 (  59 expanded)
%              Number of leaves         :   24 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :  449 ( 498 expanded)
%              Number of equality atoms :   52 (  59 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('0',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ ( k4_xboole_0 @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf(t43_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( ( C = k1_xboole_0 )
            & ( B
              = ( k1_tarski @ A ) ) )
        & ~ ( ( C
              = ( k1_tarski @ A ) )
            & ( B = k1_xboole_0 ) )
        & ~ ( ( C
              = ( k1_tarski @ A ) )
            & ( B
              = ( k1_tarski @ A ) ) )
        & ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( B
          = ( k1_tarski @ A ) )
        & ( C
          = ( k1_tarski @ A ) ) ) ) )).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( B = k1_xboole_0 )
        & ( C
          = ( k1_tarski @ A ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
     => ( ( B
          = ( k1_tarski @ A ) )
        & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_6,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( zip_tseitin_2 @ C @ B @ A )
        & ~ ( zip_tseitin_1 @ C @ B @ A )
        & ~ ( zip_tseitin_0 @ C @ B @ A ) ) )).

thf('1',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_tarski @ X28 )
       != ( k2_xboole_0 @ X26 @ X27 ) )
      | ( zip_tseitin_2 @ X27 @ X26 @ X28 )
      | ( zip_tseitin_1 @ X27 @ X26 @ X28 )
      | ( zip_tseitin_0 @ X27 @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X2 )
       != X0 )
      | ( zip_tseitin_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      | ( zip_tseitin_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      | ( zip_tseitin_2 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X1: $i,X2: $i] :
      ( ( zip_tseitin_2 @ ( k4_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) @ ( k3_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) @ X2 )
      | ( zip_tseitin_1 @ ( k4_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) @ ( k3_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) @ X2 )
      | ( zip_tseitin_0 @ ( k4_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) @ ( k3_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( X24
        = ( k1_tarski @ X23 ) )
      | ~ ( zip_tseitin_2 @ X25 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) @ X0 )
      | ( zip_tseitin_1 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) @ X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( X18
        = ( k1_tarski @ X17 ) )
      | ~ ( zip_tseitin_0 @ X19 @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( zip_tseitin_1 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( X21
        = ( k1_tarski @ X22 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t69_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_7,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
        | ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t69_zfmisc_1])).

thf('10',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('11',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('14',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ ( k4_xboole_0 @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['14','25'])).

thf('27',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('28',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2mVfQKzRoq
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:03:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 19.10/19.30  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 19.10/19.30  % Solved by: fo/fo7.sh
% 19.10/19.30  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 19.10/19.30  % done 10488 iterations in 18.822s
% 19.10/19.30  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 19.10/19.30  % SZS output start Refutation
% 19.10/19.30  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 19.10/19.30  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 19.10/19.30  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 19.10/19.30  thf(sk_B_type, type, sk_B: $i).
% 19.10/19.30  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 19.10/19.30  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 19.10/19.30  thf(sk_A_type, type, sk_A: $i).
% 19.10/19.30  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 19.10/19.30  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 19.10/19.30  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 19.10/19.30  thf(t51_xboole_1, axiom,
% 19.10/19.30    (![A:$i,B:$i]:
% 19.10/19.30     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 19.10/19.30       ( A ) ))).
% 19.10/19.30  thf('0', plain,
% 19.10/19.30      (![X14 : $i, X15 : $i]:
% 19.10/19.30         ((k2_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ (k4_xboole_0 @ X14 @ X15))
% 19.10/19.30           = (X14))),
% 19.10/19.30      inference('cnf', [status(esa)], [t51_xboole_1])).
% 19.10/19.30  thf(t43_zfmisc_1, axiom,
% 19.10/19.30    (![A:$i,B:$i,C:$i]:
% 19.10/19.30     ( ~( ( ~( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) = ( k1_tarski @ A ) ) ) ) & 
% 19.10/19.30          ( ~( ( ( C ) = ( k1_tarski @ A ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) & 
% 19.10/19.30          ( ~( ( ( C ) = ( k1_tarski @ A ) ) & ( ( B ) = ( k1_tarski @ A ) ) ) ) & 
% 19.10/19.30          ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) ) ))).
% 19.10/19.30  thf(zf_stmt_0, type, zip_tseitin_2 : $i > $i > $i > $o).
% 19.10/19.30  thf(zf_stmt_1, axiom,
% 19.10/19.30    (![C:$i,B:$i,A:$i]:
% 19.10/19.30     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 19.10/19.30       ( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ))).
% 19.10/19.30  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 19.10/19.30  thf(zf_stmt_3, axiom,
% 19.10/19.30    (![C:$i,B:$i,A:$i]:
% 19.10/19.30     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 19.10/19.30       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ))).
% 19.10/19.30  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $i > $o).
% 19.10/19.30  thf(zf_stmt_5, axiom,
% 19.10/19.30    (![C:$i,B:$i,A:$i]:
% 19.10/19.30     ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 19.10/19.30       ( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ))).
% 19.10/19.30  thf(zf_stmt_6, axiom,
% 19.10/19.30    (![A:$i,B:$i,C:$i]:
% 19.10/19.30     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 19.10/19.30          ( ~( zip_tseitin_2 @ C @ B @ A ) ) & 
% 19.10/19.30          ( ~( zip_tseitin_1 @ C @ B @ A ) ) & 
% 19.10/19.30          ( ~( zip_tseitin_0 @ C @ B @ A ) ) ) ))).
% 19.10/19.30  thf('1', plain,
% 19.10/19.30      (![X26 : $i, X27 : $i, X28 : $i]:
% 19.10/19.30         (((k1_tarski @ X28) != (k2_xboole_0 @ X26 @ X27))
% 19.10/19.30          | (zip_tseitin_2 @ X27 @ X26 @ X28)
% 19.10/19.30          | (zip_tseitin_1 @ X27 @ X26 @ X28)
% 19.10/19.30          | (zip_tseitin_0 @ X27 @ X26 @ X28))),
% 19.10/19.30      inference('cnf', [status(esa)], [zf_stmt_6])).
% 19.10/19.30  thf('2', plain,
% 19.10/19.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.10/19.30         (((k1_tarski @ X2) != (X0))
% 19.10/19.30          | (zip_tseitin_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 19.10/19.30             (k3_xboole_0 @ X0 @ X1) @ X2)
% 19.10/19.30          | (zip_tseitin_1 @ (k4_xboole_0 @ X0 @ X1) @ 
% 19.10/19.30             (k3_xboole_0 @ X0 @ X1) @ X2)
% 19.10/19.30          | (zip_tseitin_2 @ (k4_xboole_0 @ X0 @ X1) @ 
% 19.10/19.30             (k3_xboole_0 @ X0 @ X1) @ X2))),
% 19.10/19.30      inference('sup-', [status(thm)], ['0', '1'])).
% 19.10/19.30  thf('3', plain,
% 19.10/19.30      (![X1 : $i, X2 : $i]:
% 19.10/19.30         ((zip_tseitin_2 @ (k4_xboole_0 @ (k1_tarski @ X2) @ X1) @ 
% 19.10/19.30           (k3_xboole_0 @ (k1_tarski @ X2) @ X1) @ X2)
% 19.10/19.30          | (zip_tseitin_1 @ (k4_xboole_0 @ (k1_tarski @ X2) @ X1) @ 
% 19.10/19.30             (k3_xboole_0 @ (k1_tarski @ X2) @ X1) @ X2)
% 19.10/19.30          | (zip_tseitin_0 @ (k4_xboole_0 @ (k1_tarski @ X2) @ X1) @ 
% 19.10/19.30             (k3_xboole_0 @ (k1_tarski @ X2) @ X1) @ X2))),
% 19.10/19.30      inference('simplify', [status(thm)], ['2'])).
% 19.10/19.30  thf('4', plain,
% 19.10/19.30      (![X23 : $i, X24 : $i, X25 : $i]:
% 19.10/19.30         (((X24) = (k1_tarski @ X23)) | ~ (zip_tseitin_2 @ X25 @ X24 @ X23))),
% 19.10/19.30      inference('cnf', [status(esa)], [zf_stmt_1])).
% 19.10/19.30  thf('5', plain,
% 19.10/19.30      (![X0 : $i, X1 : $i]:
% 19.10/19.30         ((zip_tseitin_0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1) @ 
% 19.10/19.30           (k3_xboole_0 @ (k1_tarski @ X0) @ X1) @ X0)
% 19.10/19.30          | (zip_tseitin_1 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1) @ 
% 19.10/19.30             (k3_xboole_0 @ (k1_tarski @ X0) @ X1) @ X0)
% 19.10/19.30          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0)))),
% 19.10/19.30      inference('sup-', [status(thm)], ['3', '4'])).
% 19.10/19.30  thf('6', plain,
% 19.10/19.30      (![X17 : $i, X18 : $i, X19 : $i]:
% 19.10/19.30         (((X18) = (k1_tarski @ X17)) | ~ (zip_tseitin_0 @ X19 @ X18 @ X17))),
% 19.10/19.30      inference('cnf', [status(esa)], [zf_stmt_5])).
% 19.10/19.30  thf('7', plain,
% 19.10/19.30      (![X0 : $i, X1 : $i]:
% 19.10/19.30         (((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 19.10/19.30          | (zip_tseitin_1 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1) @ 
% 19.10/19.30             (k3_xboole_0 @ (k1_tarski @ X0) @ X1) @ X0))),
% 19.10/19.30      inference('clc', [status(thm)], ['5', '6'])).
% 19.10/19.30  thf('8', plain,
% 19.10/19.30      (![X20 : $i, X21 : $i, X22 : $i]:
% 19.10/19.30         (((X21) = (k1_tarski @ X22)) | ~ (zip_tseitin_1 @ X21 @ X20 @ X22))),
% 19.10/19.30      inference('cnf', [status(esa)], [zf_stmt_3])).
% 19.10/19.30  thf('9', plain,
% 19.10/19.30      (![X0 : $i, X1 : $i]:
% 19.10/19.30         (((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 19.10/19.30          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0)))),
% 19.10/19.30      inference('sup-', [status(thm)], ['7', '8'])).
% 19.10/19.30  thf(t69_zfmisc_1, conjecture,
% 19.10/19.30    (![A:$i,B:$i]:
% 19.10/19.30     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 19.10/19.30       ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) ))).
% 19.10/19.30  thf(zf_stmt_7, negated_conjecture,
% 19.10/19.30    (~( ![A:$i,B:$i]:
% 19.10/19.30        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 19.10/19.30          ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) ) )),
% 19.10/19.30    inference('cnf.neg', [status(esa)], [t69_zfmisc_1])).
% 19.10/19.30  thf('10', plain,
% 19.10/19.30      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 19.10/19.30      inference('cnf', [status(esa)], [zf_stmt_7])).
% 19.10/19.30  thf('11', plain,
% 19.10/19.30      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 19.10/19.30        | ((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 19.10/19.30      inference('sup-', [status(thm)], ['9', '10'])).
% 19.10/19.30  thf('12', plain,
% 19.10/19.30      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))),
% 19.10/19.30      inference('simplify', [status(thm)], ['11'])).
% 19.10/19.30  thf(t47_xboole_1, axiom,
% 19.10/19.30    (![A:$i,B:$i]:
% 19.10/19.30     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 19.10/19.30  thf('13', plain,
% 19.10/19.30      (![X10 : $i, X11 : $i]:
% 19.10/19.30         ((k4_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11))
% 19.10/19.30           = (k4_xboole_0 @ X10 @ X11))),
% 19.10/19.30      inference('cnf', [status(esa)], [t47_xboole_1])).
% 19.10/19.30  thf('14', plain,
% 19.10/19.30      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 19.10/19.30         = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 19.10/19.30      inference('sup+', [status(thm)], ['12', '13'])).
% 19.10/19.30  thf(t46_xboole_1, axiom,
% 19.10/19.30    (![A:$i,B:$i]:
% 19.10/19.30     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 19.10/19.30  thf('15', plain,
% 19.10/19.30      (![X8 : $i, X9 : $i]:
% 19.10/19.30         ((k4_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9)) = (k1_xboole_0))),
% 19.10/19.30      inference('cnf', [status(esa)], [t46_xboole_1])).
% 19.10/19.30  thf(t48_xboole_1, axiom,
% 19.10/19.30    (![A:$i,B:$i]:
% 19.10/19.30     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 19.10/19.30  thf('16', plain,
% 19.10/19.30      (![X12 : $i, X13 : $i]:
% 19.10/19.30         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 19.10/19.30           = (k3_xboole_0 @ X12 @ X13))),
% 19.10/19.30      inference('cnf', [status(esa)], [t48_xboole_1])).
% 19.10/19.30  thf('17', plain,
% 19.10/19.30      (![X0 : $i, X1 : $i]:
% 19.10/19.30         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 19.10/19.30           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 19.10/19.30      inference('sup+', [status(thm)], ['15', '16'])).
% 19.10/19.30  thf(t3_boole, axiom,
% 19.10/19.30    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 19.10/19.30  thf('18', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 19.10/19.30      inference('cnf', [status(esa)], [t3_boole])).
% 19.10/19.30  thf('19', plain,
% 19.10/19.30      (![X0 : $i, X1 : $i]:
% 19.10/19.30         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 19.10/19.30      inference('demod', [status(thm)], ['17', '18'])).
% 19.10/19.30  thf('20', plain,
% 19.10/19.30      (![X14 : $i, X15 : $i]:
% 19.10/19.30         ((k2_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ (k4_xboole_0 @ X14 @ X15))
% 19.10/19.30           = (X14))),
% 19.10/19.30      inference('cnf', [status(esa)], [t51_xboole_1])).
% 19.10/19.30  thf('21', plain,
% 19.10/19.30      (![X0 : $i, X1 : $i]:
% 19.10/19.30         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))
% 19.10/19.30           = (X0))),
% 19.10/19.30      inference('sup+', [status(thm)], ['19', '20'])).
% 19.10/19.30  thf('22', plain,
% 19.10/19.30      (![X8 : $i, X9 : $i]:
% 19.10/19.30         ((k4_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9)) = (k1_xboole_0))),
% 19.10/19.30      inference('cnf', [status(esa)], [t46_xboole_1])).
% 19.10/19.30  thf('23', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 19.10/19.30      inference('demod', [status(thm)], ['21', '22'])).
% 19.10/19.30  thf('24', plain,
% 19.10/19.30      (![X8 : $i, X9 : $i]:
% 19.10/19.30         ((k4_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9)) = (k1_xboole_0))),
% 19.10/19.30      inference('cnf', [status(esa)], [t46_xboole_1])).
% 19.10/19.30  thf('25', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 19.10/19.30      inference('sup+', [status(thm)], ['23', '24'])).
% 19.10/19.30  thf('26', plain,
% 19.10/19.30      (((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 19.10/19.30      inference('demod', [status(thm)], ['14', '25'])).
% 19.10/19.30  thf('27', plain,
% 19.10/19.30      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0))),
% 19.10/19.30      inference('cnf', [status(esa)], [zf_stmt_7])).
% 19.10/19.30  thf('28', plain, ($false),
% 19.10/19.30      inference('simplify_reflect-', [status(thm)], ['26', '27'])).
% 19.10/19.30  
% 19.10/19.30  % SZS output end Refutation
% 19.10/19.30  
% 19.10/19.31  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
