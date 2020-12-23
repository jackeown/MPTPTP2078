%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Xqw64TM4A7

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   49 (  67 expanded)
%              Number of leaves         :   18 (  27 expanded)
%              Depth                    :   13
%              Number of atoms          :  387 ( 729 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t73_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ A @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k2_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
            & ( r2_hidden @ A @ B ) )
         => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k2_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t73_funct_1])).

thf('0',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t72_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ B )
       => ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k1_funct_1 @ C @ A ) ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X16 @ X15 ) @ X14 )
        = ( k1_funct_1 @ X16 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t72_funct_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k7_relat_1 @ X0 @ sk_B ) @ sk_A )
        = ( k1_funct_1 @ X0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(fc8_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('6',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_A @ X0 )
      | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X8 ) @ X9 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X13 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X13 @ X12 ) @ ( k2_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) )
    | ( r2_hidden @ ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) )
    | ( r2_hidden @ ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r2_hidden @ ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['4','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r2_hidden @ ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['3','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['0','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Xqw64TM4A7
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % DateTime   : Tue Dec  1 09:31:36 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 155 iterations in 0.059s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.51  thf(t73_funct_1, conjecture,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.51       ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & ( r2_hidden @ A @ B ) ) =>
% 0.20/0.51         ( r2_hidden @
% 0.20/0.51           ( k1_funct_1 @ C @ A ) @ ( k2_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.51        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.51          ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & ( r2_hidden @ A @ B ) ) =>
% 0.20/0.51            ( r2_hidden @
% 0.20/0.51              ( k1_funct_1 @ C @ A ) @ ( k2_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t73_funct_1])).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      (~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ 
% 0.20/0.51          (k2_relat_1 @ (k7_relat_1 @ sk_C @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t72_funct_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.51       ( ( r2_hidden @ A @ B ) =>
% 0.20/0.51         ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k1_funct_1 @ C @ A ) ) ) ))).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X14 @ X15)
% 0.20/0.51          | ~ (v1_relat_1 @ X16)
% 0.20/0.51          | ~ (v1_funct_1 @ X16)
% 0.20/0.51          | ((k1_funct_1 @ (k7_relat_1 @ X16 @ X15) @ X14)
% 0.20/0.51              = (k1_funct_1 @ X16 @ X14)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t72_funct_1])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((k1_funct_1 @ (k7_relat_1 @ X0 @ sk_B) @ sk_A)
% 0.20/0.51            = (k1_funct_1 @ X0 @ sk_A))
% 0.20/0.51          | ~ (v1_funct_1 @ X0)
% 0.20/0.51          | ~ (v1_relat_1 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.51  thf(dt_k7_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ X6) | (v1_relat_1 @ (k7_relat_1 @ X6 @ X7)))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.20/0.51  thf(fc8_funct_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.51       ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) & 
% 0.20/0.51         ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X10 : $i, X11 : $i]:
% 0.20/0.51         (~ (v1_funct_1 @ X10)
% 0.20/0.51          | ~ (v1_relat_1 @ X10)
% 0.20/0.51          | (v1_funct_1 @ (k7_relat_1 @ X10 @ X11)))),
% 0.20/0.51      inference('cnf', [status(esa)], [fc8_funct_1])).
% 0.20/0.51  thf('6', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('7', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(d4_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.20/0.51       ( ![D:$i]:
% 0.20/0.51         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.51           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.51          | ~ (r2_hidden @ X0 @ X2)
% 0.20/0.51          | (r2_hidden @ X0 @ X3)
% 0.20/0.51          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ X2)
% 0.20/0.51          | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.51      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (r2_hidden @ sk_A @ X0)
% 0.20/0.51          | (r2_hidden @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['7', '9'])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      ((r2_hidden @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_C) @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['6', '10'])).
% 0.20/0.51  thf(t90_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ B ) =>
% 0.20/0.51       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.20/0.51         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i]:
% 0.20/0.51         (((k1_relat_1 @ (k7_relat_1 @ X8 @ X9))
% 0.20/0.51            = (k3_xboole_0 @ (k1_relat_1 @ X8) @ X9))
% 0.20/0.51          | ~ (v1_relat_1 @ X8))),
% 0.20/0.51      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.20/0.51  thf(t12_funct_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.51       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.51         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X12 @ (k1_relat_1 @ X13))
% 0.20/0.51          | (r2_hidden @ (k1_funct_1 @ X13 @ X12) @ (k2_relat_1 @ X13))
% 0.20/0.51          | ~ (v1_funct_1 @ X13)
% 0.20/0.51          | ~ (v1_relat_1 @ X13))),
% 0.20/0.51      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.20/0.51          | ~ (v1_relat_1 @ X1)
% 0.20/0.51          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.20/0.51          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 0.20/0.51          | (r2_hidden @ (k1_funct_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 0.20/0.51             (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (((r2_hidden @ (k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A) @ 
% 0.20/0.51         (k2_relat_1 @ (k7_relat_1 @ sk_C @ sk_B)))
% 0.20/0.51        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B))
% 0.20/0.51        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_B))
% 0.20/0.51        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['11', '14'])).
% 0.20/0.51  thf('16', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (((r2_hidden @ (k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A) @ 
% 0.20/0.51         (k2_relat_1 @ (k7_relat_1 @ sk_C @ sk_B)))
% 0.20/0.51        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B))
% 0.20/0.51        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.51        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.51        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_B))
% 0.20/0.51        | (r2_hidden @ (k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A) @ 
% 0.20/0.51           (k2_relat_1 @ (k7_relat_1 @ sk_C @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['5', '17'])).
% 0.20/0.51  thf('19', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      ((~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_B))
% 0.20/0.51        | (r2_hidden @ (k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A) @ 
% 0.20/0.51           (k2_relat_1 @ (k7_relat_1 @ sk_C @ sk_B))))),
% 0.20/0.51      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.51        | (r2_hidden @ (k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A) @ 
% 0.20/0.51           (k2_relat_1 @ (k7_relat_1 @ sk_C @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '21'])).
% 0.20/0.51  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      ((r2_hidden @ (k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A) @ 
% 0.20/0.51        (k2_relat_1 @ (k7_relat_1 @ sk_C @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ 
% 0.20/0.51         (k2_relat_1 @ (k7_relat_1 @ sk_C @ sk_B)))
% 0.20/0.51        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.51        | ~ (v1_funct_1 @ sk_C))),
% 0.20/0.51      inference('sup+', [status(thm)], ['3', '24'])).
% 0.20/0.51  thf('26', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('27', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ 
% 0.20/0.51        (k2_relat_1 @ (k7_relat_1 @ sk_C @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.20/0.51  thf('29', plain, ($false), inference('demod', [status(thm)], ['0', '28'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
