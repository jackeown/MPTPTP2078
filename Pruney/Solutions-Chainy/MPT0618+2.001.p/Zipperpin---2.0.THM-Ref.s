%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2muuwhTMKQ

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   43 (  83 expanded)
%              Number of leaves         :   13 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  326 ( 934 expanded)
%              Number of equality atoms :   14 (  36 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t12_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
         => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t12_funct_1])).

thf('0',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X3 @ ( k1_relat_1 @ X4 ) )
      | ( X5 = k1_xboole_0 )
      | ( X5
       != ( k1_funct_1 @ X4 @ X3 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( ( k1_funct_1 @ X4 @ X3 )
        = k1_xboole_0 )
      | ( r2_hidden @ X3 @ ( k1_relat_1 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k1_relat_1 @ X4 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X6 ) @ X4 )
      | ( X6
       != ( k1_funct_1 @ X4 @ X3 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( k1_funct_1 @ X4 @ X3 ) ) @ X4 )
      | ~ ( r2_hidden @ X3 @ ( k1_relat_1 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_funct_1 @ X0 @ X1 ) ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_funct_1 @ X0 @ X1 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ X1 @ ( k2_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k1_funct_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ~ ( r2_hidden @ k1_xboole_0 @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','14'])).

thf('16',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( k1_funct_1 @ X4 @ X3 ) ) @ X4 )
      | ~ ( r2_hidden @ X3 @ ( k1_relat_1 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('18',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ X1 @ ( k2_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k1_funct_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('27',plain,(
    r2_hidden @ k1_xboole_0 @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    $false ),
    inference(demod,[status(thm)],['15','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2muuwhTMKQ
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:20:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 21 iterations in 0.019s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.47  thf(t12_funct_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.47       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.47         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i]:
% 0.20/0.47        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.47          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.47            ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t12_funct_1])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      (~ (r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(d4_funct_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.47       ( ![B:$i,C:$i]:
% 0.20/0.47         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.20/0.47             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.20/0.47               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.47           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.20/0.47             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.20/0.47               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.47         ((r2_hidden @ X3 @ (k1_relat_1 @ X4))
% 0.20/0.47          | ((X5) = (k1_xboole_0))
% 0.20/0.47          | ((X5) != (k1_funct_1 @ X4 @ X3))
% 0.20/0.47          | ~ (v1_funct_1 @ X4)
% 0.20/0.47          | ~ (v1_relat_1 @ X4))),
% 0.20/0.47      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X4)
% 0.20/0.47          | ~ (v1_funct_1 @ X4)
% 0.20/0.47          | ((k1_funct_1 @ X4 @ X3) = (k1_xboole_0))
% 0.20/0.47          | (r2_hidden @ X3 @ (k1_relat_1 @ X4)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['1'])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X3 @ (k1_relat_1 @ X4))
% 0.20/0.47          | (r2_hidden @ (k4_tarski @ X3 @ X6) @ X4)
% 0.20/0.47          | ((X6) != (k1_funct_1 @ X4 @ X3))
% 0.20/0.47          | ~ (v1_funct_1 @ X4)
% 0.20/0.47          | ~ (v1_relat_1 @ X4))),
% 0.20/0.47      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X4)
% 0.20/0.47          | ~ (v1_funct_1 @ X4)
% 0.20/0.47          | (r2_hidden @ (k4_tarski @ X3 @ (k1_funct_1 @ X4 @ X3)) @ X4)
% 0.20/0.47          | ~ (r2_hidden @ X3 @ (k1_relat_1 @ X4)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (((k1_funct_1 @ X0 @ X1) = (k1_xboole_0))
% 0.20/0.47          | ~ (v1_funct_1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X0)
% 0.20/0.47          | (r2_hidden @ (k4_tarski @ X1 @ (k1_funct_1 @ X0 @ X1)) @ X0)
% 0.20/0.47          | ~ (v1_funct_1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['2', '4'])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((r2_hidden @ (k4_tarski @ X1 @ (k1_funct_1 @ X0 @ X1)) @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X0)
% 0.20/0.47          | ~ (v1_funct_1 @ X0)
% 0.20/0.47          | ((k1_funct_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.47  thf(t20_relat_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ C ) =>
% 0.20/0.47       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.20/0.47         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.47           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (r2_hidden @ (k4_tarski @ X0 @ X1) @ X2)
% 0.20/0.47          | (r2_hidden @ X1 @ (k2_relat_1 @ X2))
% 0.20/0.47          | ~ (v1_relat_1 @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (((k1_funct_1 @ X0 @ X1) = (k1_xboole_0))
% 0.20/0.47          | ~ (v1_funct_1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X0)
% 0.20/0.47          | (r2_hidden @ (k1_funct_1 @ X0 @ X1) @ (k2_relat_1 @ X0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((r2_hidden @ (k1_funct_1 @ X0 @ X1) @ (k2_relat_1 @ X0))
% 0.20/0.47          | ~ (v1_relat_1 @ X0)
% 0.20/0.47          | ~ (v1_funct_1 @ X0)
% 0.20/0.47          | ((k1_funct_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (~ (r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      ((((k1_funct_1 @ sk_B @ sk_A) = (k1_xboole_0))
% 0.20/0.47        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.47        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.47  thf('12', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('13', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('14', plain, (((k1_funct_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.20/0.47      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.20/0.47  thf('15', plain, (~ (r2_hidden @ k1_xboole_0 @ (k2_relat_1 @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['0', '14'])).
% 0.20/0.47  thf('16', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X4)
% 0.20/0.47          | ~ (v1_funct_1 @ X4)
% 0.20/0.47          | (r2_hidden @ (k4_tarski @ X3 @ (k1_funct_1 @ X4 @ X3)) @ X4)
% 0.20/0.47          | ~ (r2_hidden @ X3 @ (k1_relat_1 @ X4)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)
% 0.20/0.47        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.47        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.47  thf('19', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('20', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      ((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)),
% 0.20/0.47      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (r2_hidden @ (k4_tarski @ X0 @ X1) @ X2)
% 0.20/0.47          | (r2_hidden @ X1 @ (k2_relat_1 @ X2))
% 0.20/0.47          | ~ (v1_relat_1 @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.47        | (r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.47  thf('24', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      ((r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.47  thf('26', plain, (((k1_funct_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.20/0.47      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.20/0.47  thf('27', plain, ((r2_hidden @ k1_xboole_0 @ (k2_relat_1 @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.47  thf('28', plain, ($false), inference('demod', [status(thm)], ['15', '27'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
