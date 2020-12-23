%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.I4c69CfZ5i

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   53 (  83 expanded)
%              Number of leaves         :   14 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :  448 (1086 expanded)
%              Number of equality atoms :   24 (  54 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t46_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( v2_funct_1 @ B ) )
           => ( v2_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) ) )).

thf('0',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X8 @ X7 ) )
      | ~ ( v2_funct_1 @ X7 )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t46_funct_1])).

thf(fc2_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_funct_1 @ X4 )
        = ( k4_relat_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X2 ) @ ( k4_relat_1 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf(t66_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( v2_funct_1 @ B ) )
           => ( ( k2_funct_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k5_relat_1 @ ( k2_funct_1 @ B ) @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ( ( ( v2_funct_1 @ A )
                & ( v2_funct_1 @ B ) )
             => ( ( k2_funct_1 @ ( k5_relat_1 @ A @ B ) )
                = ( k5_relat_1 @ ( k2_funct_1 @ B ) @ ( k2_funct_1 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_funct_1])).

thf('10',plain,(
    ( k2_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
 != ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_funct_1 @ X4 )
        = ( k4_relat_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ( ( k2_funct_1 @ sk_A )
      = ( k4_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ( k2_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
 != ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k4_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_funct_1 @ X4 )
        = ( k4_relat_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('20',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k2_funct_1 @ sk_B )
      = ( k4_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k2_funct_1 @ sk_B )
    = ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ( k2_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
 != ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k4_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','23'])).

thf('25',plain,
    ( ( ( k2_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
     != ( k4_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['9','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ( k2_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
 != ( k4_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ( ( k4_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
     != ( k4_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ( k4_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
 != ( k4_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30','31','32','33','34','35'])).

thf('37',plain,(
    $false ),
    inference(simplify,[status(thm)],['36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.I4c69CfZ5i
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:24:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 23 iterations in 0.018s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.47  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.47  thf(t46_funct_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.47           ( ( ( v2_funct_1 @ A ) & ( v2_funct_1 @ B ) ) =>
% 0.21/0.47             ( v2_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      (![X7 : $i, X8 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X7)
% 0.21/0.47          | ~ (v1_funct_1 @ X7)
% 0.21/0.47          | (v2_funct_1 @ (k5_relat_1 @ X8 @ X7))
% 0.21/0.47          | ~ (v2_funct_1 @ X7)
% 0.21/0.47          | ~ (v2_funct_1 @ X8)
% 0.21/0.47          | ~ (v1_funct_1 @ X8)
% 0.21/0.47          | ~ (v1_relat_1 @ X8))),
% 0.21/0.47      inference('cnf', [status(esa)], [t46_funct_1])).
% 0.21/0.47  thf(fc2_funct_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v1_relat_1 @ B ) & 
% 0.21/0.47         ( v1_funct_1 @ B ) ) =>
% 0.21/0.47       ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) & 
% 0.21/0.47         ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X5 : $i, X6 : $i]:
% 0.21/0.47         (~ (v1_funct_1 @ X5)
% 0.21/0.47          | ~ (v1_relat_1 @ X5)
% 0.21/0.47          | ~ (v1_relat_1 @ X6)
% 0.21/0.47          | ~ (v1_funct_1 @ X6)
% 0.21/0.47          | (v1_funct_1 @ (k5_relat_1 @ X5 @ X6)))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.21/0.47  thf(dt_k5_relat_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.21/0.47       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X0)
% 0.21/0.47          | ~ (v1_relat_1 @ X1)
% 0.21/0.47          | (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.21/0.47  thf(d9_funct_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.47       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X4 : $i]:
% 0.21/0.47         (~ (v2_funct_1 @ X4)
% 0.21/0.47          | ((k2_funct_1 @ X4) = (k4_relat_1 @ X4))
% 0.21/0.47          | ~ (v1_funct_1 @ X4)
% 0.21/0.47          | ~ (v1_relat_1 @ X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X0)
% 0.21/0.47          | ~ (v1_relat_1 @ X1)
% 0.21/0.47          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.21/0.47          | ((k2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.21/0.47              = (k4_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.21/0.47          | ~ (v2_funct_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (v1_funct_1 @ X0)
% 0.21/0.47          | ~ (v1_relat_1 @ X0)
% 0.21/0.47          | ~ (v1_relat_1 @ X1)
% 0.21/0.47          | ~ (v1_funct_1 @ X1)
% 0.21/0.47          | ~ (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.21/0.47          | ((k2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.21/0.47              = (k4_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.21/0.47          | ~ (v1_relat_1 @ X1)
% 0.21/0.47          | ~ (v1_relat_1 @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '4'])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (((k2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.21/0.47            = (k4_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.21/0.47          | ~ (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.21/0.47          | ~ (v1_funct_1 @ X1)
% 0.21/0.47          | ~ (v1_relat_1 @ X1)
% 0.21/0.47          | ~ (v1_relat_1 @ X0)
% 0.21/0.47          | ~ (v1_funct_1 @ X0))),
% 0.21/0.47      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X1)
% 0.21/0.47          | ~ (v1_funct_1 @ X1)
% 0.21/0.47          | ~ (v2_funct_1 @ X1)
% 0.21/0.47          | ~ (v2_funct_1 @ X0)
% 0.21/0.47          | ~ (v1_funct_1 @ X0)
% 0.21/0.47          | ~ (v1_relat_1 @ X0)
% 0.21/0.47          | ~ (v1_funct_1 @ X0)
% 0.21/0.47          | ~ (v1_relat_1 @ X0)
% 0.21/0.47          | ~ (v1_relat_1 @ X1)
% 0.21/0.47          | ~ (v1_funct_1 @ X1)
% 0.21/0.47          | ((k2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.21/0.47              = (k4_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '6'])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (((k2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.21/0.47            = (k4_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.21/0.47          | ~ (v1_relat_1 @ X0)
% 0.21/0.47          | ~ (v1_funct_1 @ X0)
% 0.21/0.47          | ~ (v2_funct_1 @ X0)
% 0.21/0.47          | ~ (v2_funct_1 @ X1)
% 0.21/0.47          | ~ (v1_funct_1 @ X1)
% 0.21/0.47          | ~ (v1_relat_1 @ X1))),
% 0.21/0.47      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.47  thf(t54_relat_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( v1_relat_1 @ B ) =>
% 0.21/0.47           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.21/0.47             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X2 : $i, X3 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X2)
% 0.21/0.47          | ((k4_relat_1 @ (k5_relat_1 @ X3 @ X2))
% 0.21/0.47              = (k5_relat_1 @ (k4_relat_1 @ X2) @ (k4_relat_1 @ X3)))
% 0.21/0.47          | ~ (v1_relat_1 @ X3))),
% 0.21/0.47      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.21/0.47  thf(t66_funct_1, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.47           ( ( ( v2_funct_1 @ A ) & ( v2_funct_1 @ B ) ) =>
% 0.21/0.47             ( ( k2_funct_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.21/0.47               ( k5_relat_1 @ ( k2_funct_1 @ B ) @ ( k2_funct_1 @ A ) ) ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.47          ( ![B:$i]:
% 0.21/0.47            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.47              ( ( ( v2_funct_1 @ A ) & ( v2_funct_1 @ B ) ) =>
% 0.21/0.47                ( ( k2_funct_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.21/0.47                  ( k5_relat_1 @ ( k2_funct_1 @ B ) @ ( k2_funct_1 @ A ) ) ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t66_funct_1])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (((k2_funct_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 0.21/0.47         != (k5_relat_1 @ (k2_funct_1 @ sk_B) @ (k2_funct_1 @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('11', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X4 : $i]:
% 0.21/0.47         (~ (v2_funct_1 @ X4)
% 0.21/0.47          | ((k2_funct_1 @ X4) = (k4_relat_1 @ X4))
% 0.21/0.47          | ~ (v1_funct_1 @ X4)
% 0.21/0.47          | ~ (v1_relat_1 @ X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      ((~ (v1_funct_1 @ sk_A)
% 0.21/0.47        | ((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))
% 0.21/0.47        | ~ (v2_funct_1 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.47  thf('14', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('15', plain, ((v2_funct_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('16', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (((k2_funct_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 0.21/0.47         != (k5_relat_1 @ (k2_funct_1 @ sk_B) @ (k4_relat_1 @ sk_A)))),
% 0.21/0.47      inference('demod', [status(thm)], ['10', '16'])).
% 0.21/0.47  thf('18', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (![X4 : $i]:
% 0.21/0.47         (~ (v2_funct_1 @ X4)
% 0.21/0.47          | ((k2_funct_1 @ X4) = (k4_relat_1 @ X4))
% 0.21/0.47          | ~ (v1_funct_1 @ X4)
% 0.21/0.47          | ~ (v1_relat_1 @ X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      ((~ (v1_funct_1 @ sk_B)
% 0.21/0.47        | ((k2_funct_1 @ sk_B) = (k4_relat_1 @ sk_B))
% 0.21/0.47        | ~ (v2_funct_1 @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.47  thf('21', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('22', plain, ((v2_funct_1 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('23', plain, (((k2_funct_1 @ sk_B) = (k4_relat_1 @ sk_B))),
% 0.21/0.47      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.21/0.47  thf('24', plain,
% 0.21/0.47      (((k2_funct_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 0.21/0.47         != (k5_relat_1 @ (k4_relat_1 @ sk_B) @ (k4_relat_1 @ sk_A)))),
% 0.21/0.47      inference('demod', [status(thm)], ['17', '23'])).
% 0.21/0.47  thf('25', plain,
% 0.21/0.47      ((((k2_funct_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 0.21/0.47          != (k4_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))
% 0.21/0.47        | ~ (v1_relat_1 @ sk_A)
% 0.21/0.47        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['9', '24'])).
% 0.21/0.47  thf('26', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('27', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('28', plain,
% 0.21/0.47      (((k2_funct_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 0.21/0.47         != (k4_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))),
% 0.21/0.47      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.21/0.47  thf('29', plain,
% 0.21/0.47      ((((k4_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 0.21/0.47          != (k4_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))
% 0.21/0.47        | ~ (v1_relat_1 @ sk_A)
% 0.21/0.47        | ~ (v1_funct_1 @ sk_A)
% 0.21/0.47        | ~ (v2_funct_1 @ sk_A)
% 0.21/0.47        | ~ (v2_funct_1 @ sk_B)
% 0.21/0.47        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.47        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['8', '28'])).
% 0.21/0.47  thf('30', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('31', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('32', plain, ((v2_funct_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('33', plain, ((v2_funct_1 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('34', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('35', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('36', plain,
% 0.21/0.47      (((k4_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 0.21/0.47         != (k4_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))),
% 0.21/0.47      inference('demod', [status(thm)],
% 0.21/0.47                ['29', '30', '31', '32', '33', '34', '35'])).
% 0.21/0.47  thf('37', plain, ($false), inference('simplify', [status(thm)], ['36'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
