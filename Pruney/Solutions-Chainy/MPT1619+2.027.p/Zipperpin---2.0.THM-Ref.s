%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uXXH2EjJTr

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:27 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   49 (  58 expanded)
%              Number of leaves         :   21 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  313 ( 419 expanded)
%              Number of equality atoms :   19 (  25 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_yellow_1_type,type,(
    v1_yellow_1: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k6_yellow_1_type,type,(
    k6_yellow_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_funcop_1_type,type,(
    k7_funcop_1: $i > $i > $i )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_funcop_1_type,type,(
    k2_funcop_1: $i > $i > $i )).

thf(k5_yellow_1_type,type,(
    k5_yellow_1: $i > $i > $i )).

thf(d5_yellow_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ B )
     => ( ( k6_yellow_1 @ A @ B )
        = ( k5_yellow_1 @ A @ ( k7_funcop_1 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_yellow_1 @ X0 @ X1 )
        = ( k5_yellow_1 @ X0 @ ( k7_funcop_1 @ X0 @ X1 ) ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d5_yellow_1])).

thf(fc10_yellow_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ B )
     => ( v1_yellow_1 @ ( k2_funcop_1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( v1_yellow_1 @ ( k2_funcop_1 @ X2 @ X3 ) )
      | ~ ( l1_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc10_yellow_1])).

thf(redefinition_k7_funcop_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k7_funcop_1 @ A @ B )
      = ( k2_funcop_1 @ A @ B ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k7_funcop_1 @ X9 @ X10 )
      = ( k2_funcop_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_funcop_1])).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( v1_yellow_1 @ ( k7_funcop_1 @ X2 @ X3 ) )
      | ~ ( l1_orders_2 @ X3 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(fc20_funcop_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_partfun1 @ ( k2_funcop_1 @ A @ B ) @ A )
      & ( v1_funct_1 @ ( k2_funcop_1 @ A @ B ) )
      & ( v4_relat_1 @ ( k2_funcop_1 @ A @ B ) @ A )
      & ( v1_relat_1 @ ( k2_funcop_1 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X8: $i] :
      ( v1_partfun1 @ ( k2_funcop_1 @ X4 @ X8 ) @ X4 ) ),
    inference(cnf,[status(esa)],[fc20_funcop_1])).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k7_funcop_1 @ X9 @ X10 )
      = ( k2_funcop_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_funcop_1])).

thf('6',plain,(
    ! [X4: $i,X8: $i] :
      ( v1_partfun1 @ ( k7_funcop_1 @ X4 @ X8 ) @ X4 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t26_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v4_relat_1 @ A @ k1_xboole_0 )
        & ( v1_funct_1 @ A )
        & ( v1_partfun1 @ A @ k1_xboole_0 )
        & ( v1_yellow_1 @ A ) )
     => ( ( k5_yellow_1 @ k1_xboole_0 @ A )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) )).

thf('7',plain,(
    ! [X11: $i] :
      ( ( ( k5_yellow_1 @ k1_xboole_0 @ X11 )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) )
      | ~ ( v1_yellow_1 @ X11 )
      | ~ ( v1_partfun1 @ X11 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v4_relat_1 @ X11 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t26_yellow_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_funcop_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v4_relat_1 @ ( k7_funcop_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ ( k7_funcop_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_yellow_1 @ ( k7_funcop_1 @ k1_xboole_0 @ X0 ) )
      | ( ( k5_yellow_1 @ k1_xboole_0 @ ( k7_funcop_1 @ k1_xboole_0 @ X0 ) )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_funcop_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc20_funcop_1])).

thf('10',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k7_funcop_1 @ X9 @ X10 )
      = ( k2_funcop_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_funcop_1])).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k7_funcop_1 @ X4 @ X5 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X4: $i,X6: $i] :
      ( v4_relat_1 @ ( k2_funcop_1 @ X4 @ X6 ) @ X4 ) ),
    inference(cnf,[status(esa)],[fc20_funcop_1])).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k7_funcop_1 @ X9 @ X10 )
      = ( k2_funcop_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_funcop_1])).

thf('14',plain,(
    ! [X4: $i,X6: $i] :
      ( v4_relat_1 @ ( k7_funcop_1 @ X4 @ X6 ) @ X4 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X4: $i,X7: $i] :
      ( v1_funct_1 @ ( k2_funcop_1 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc20_funcop_1])).

thf('16',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k7_funcop_1 @ X9 @ X10 )
      = ( k2_funcop_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_funcop_1])).

thf('17',plain,(
    ! [X4: $i,X7: $i] :
      ( v1_funct_1 @ ( k7_funcop_1 @ X4 @ X7 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_yellow_1 @ ( k7_funcop_1 @ k1_xboole_0 @ X0 ) )
      | ( ( k5_yellow_1 @ k1_xboole_0 @ ( k7_funcop_1 @ k1_xboole_0 @ X0 ) )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['8','11','14','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k5_yellow_1 @ k1_xboole_0 @ ( k7_funcop_1 @ k1_xboole_0 @ X0 ) )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['3','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ X0 )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k6_yellow_1 @ k1_xboole_0 @ X0 )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t27_yellow_1,conjecture,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k6_yellow_1 @ k1_xboole_0 @ A )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_orders_2 @ A )
       => ( ( k6_yellow_1 @ k1_xboole_0 @ A )
          = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_yellow_1])).

thf('22',plain,(
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
 != ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
       != ( k6_yellow_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( l1_orders_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['23'])).

thf('25',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    $false ),
    inference(demod,[status(thm)],['24','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uXXH2EjJTr
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:06:33 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 19 iterations in 0.016s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(v1_yellow_1_type, type, v1_yellow_1: $i > $o).
% 0.19/0.46  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.19/0.46  thf(k6_yellow_1_type, type, k6_yellow_1: $i > $i > $i).
% 0.19/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.46  thf(k7_funcop_1_type, type, k7_funcop_1: $i > $i > $i).
% 0.19/0.46  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.46  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.19/0.46  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.19/0.46  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.19/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.46  thf(k2_funcop_1_type, type, k2_funcop_1: $i > $i > $i).
% 0.19/0.46  thf(k5_yellow_1_type, type, k5_yellow_1: $i > $i > $i).
% 0.19/0.46  thf(d5_yellow_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( l1_orders_2 @ B ) =>
% 0.19/0.46       ( ( k6_yellow_1 @ A @ B ) =
% 0.19/0.46         ( k5_yellow_1 @ A @ ( k7_funcop_1 @ A @ B ) ) ) ))).
% 0.19/0.46  thf('0', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (((k6_yellow_1 @ X0 @ X1)
% 0.19/0.46            = (k5_yellow_1 @ X0 @ (k7_funcop_1 @ X0 @ X1)))
% 0.19/0.46          | ~ (l1_orders_2 @ X1))),
% 0.19/0.46      inference('cnf', [status(esa)], [d5_yellow_1])).
% 0.19/0.46  thf(fc10_yellow_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( l1_orders_2 @ B ) => ( v1_yellow_1 @ ( k2_funcop_1 @ A @ B ) ) ))).
% 0.19/0.46  thf('1', plain,
% 0.19/0.46      (![X2 : $i, X3 : $i]:
% 0.19/0.46         ((v1_yellow_1 @ (k2_funcop_1 @ X2 @ X3)) | ~ (l1_orders_2 @ X3))),
% 0.19/0.46      inference('cnf', [status(esa)], [fc10_yellow_1])).
% 0.19/0.46  thf(redefinition_k7_funcop_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]: ( ( k7_funcop_1 @ A @ B ) = ( k2_funcop_1 @ A @ B ) ))).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      (![X9 : $i, X10 : $i]:
% 0.19/0.46         ((k7_funcop_1 @ X9 @ X10) = (k2_funcop_1 @ X9 @ X10))),
% 0.19/0.46      inference('cnf', [status(esa)], [redefinition_k7_funcop_1])).
% 0.19/0.46  thf('3', plain,
% 0.19/0.46      (![X2 : $i, X3 : $i]:
% 0.19/0.46         ((v1_yellow_1 @ (k7_funcop_1 @ X2 @ X3)) | ~ (l1_orders_2 @ X3))),
% 0.19/0.46      inference('demod', [status(thm)], ['1', '2'])).
% 0.19/0.46  thf(fc20_funcop_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( v1_partfun1 @ ( k2_funcop_1 @ A @ B ) @ A ) & 
% 0.19/0.46       ( v1_funct_1 @ ( k2_funcop_1 @ A @ B ) ) & 
% 0.19/0.46       ( v4_relat_1 @ ( k2_funcop_1 @ A @ B ) @ A ) & 
% 0.19/0.46       ( v1_relat_1 @ ( k2_funcop_1 @ A @ B ) ) ))).
% 0.19/0.46  thf('4', plain,
% 0.19/0.46      (![X4 : $i, X8 : $i]: (v1_partfun1 @ (k2_funcop_1 @ X4 @ X8) @ X4)),
% 0.19/0.46      inference('cnf', [status(esa)], [fc20_funcop_1])).
% 0.19/0.46  thf('5', plain,
% 0.19/0.46      (![X9 : $i, X10 : $i]:
% 0.19/0.46         ((k7_funcop_1 @ X9 @ X10) = (k2_funcop_1 @ X9 @ X10))),
% 0.19/0.46      inference('cnf', [status(esa)], [redefinition_k7_funcop_1])).
% 0.19/0.46  thf('6', plain,
% 0.19/0.46      (![X4 : $i, X8 : $i]: (v1_partfun1 @ (k7_funcop_1 @ X4 @ X8) @ X4)),
% 0.19/0.46      inference('demod', [status(thm)], ['4', '5'])).
% 0.19/0.46  thf(t26_yellow_1, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( ( v1_relat_1 @ A ) & ( v4_relat_1 @ A @ k1_xboole_0 ) & 
% 0.19/0.46         ( v1_funct_1 @ A ) & ( v1_partfun1 @ A @ k1_xboole_0 ) & 
% 0.19/0.46         ( v1_yellow_1 @ A ) ) =>
% 0.19/0.46       ( ( k5_yellow_1 @ k1_xboole_0 @ A ) =
% 0.19/0.46         ( g1_orders_2 @
% 0.19/0.46           ( k1_tarski @ k1_xboole_0 ) @ 
% 0.19/0.46           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 0.19/0.46  thf('7', plain,
% 0.19/0.46      (![X11 : $i]:
% 0.19/0.46         (((k5_yellow_1 @ k1_xboole_0 @ X11)
% 0.19/0.46            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.19/0.46               (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))
% 0.19/0.46          | ~ (v1_yellow_1 @ X11)
% 0.19/0.46          | ~ (v1_partfun1 @ X11 @ k1_xboole_0)
% 0.19/0.46          | ~ (v1_funct_1 @ X11)
% 0.19/0.46          | ~ (v4_relat_1 @ X11 @ k1_xboole_0)
% 0.19/0.46          | ~ (v1_relat_1 @ X11))),
% 0.19/0.46      inference('cnf', [status(esa)], [t26_yellow_1])).
% 0.19/0.46  thf('8', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (~ (v1_relat_1 @ (k7_funcop_1 @ k1_xboole_0 @ X0))
% 0.19/0.46          | ~ (v4_relat_1 @ (k7_funcop_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.19/0.46          | ~ (v1_funct_1 @ (k7_funcop_1 @ k1_xboole_0 @ X0))
% 0.19/0.46          | ~ (v1_yellow_1 @ (k7_funcop_1 @ k1_xboole_0 @ X0))
% 0.19/0.46          | ((k5_yellow_1 @ k1_xboole_0 @ (k7_funcop_1 @ k1_xboole_0 @ X0))
% 0.19/0.46              = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.19/0.46                 (k6_partfun1 @ (k1_tarski @ k1_xboole_0)))))),
% 0.19/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.46  thf('9', plain,
% 0.19/0.46      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_funcop_1 @ X4 @ X5))),
% 0.19/0.46      inference('cnf', [status(esa)], [fc20_funcop_1])).
% 0.19/0.46  thf('10', plain,
% 0.19/0.46      (![X9 : $i, X10 : $i]:
% 0.19/0.46         ((k7_funcop_1 @ X9 @ X10) = (k2_funcop_1 @ X9 @ X10))),
% 0.19/0.46      inference('cnf', [status(esa)], [redefinition_k7_funcop_1])).
% 0.19/0.46  thf('11', plain,
% 0.19/0.46      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k7_funcop_1 @ X4 @ X5))),
% 0.19/0.46      inference('demod', [status(thm)], ['9', '10'])).
% 0.19/0.46  thf('12', plain,
% 0.19/0.46      (![X4 : $i, X6 : $i]: (v4_relat_1 @ (k2_funcop_1 @ X4 @ X6) @ X4)),
% 0.19/0.46      inference('cnf', [status(esa)], [fc20_funcop_1])).
% 0.19/0.46  thf('13', plain,
% 0.19/0.46      (![X9 : $i, X10 : $i]:
% 0.19/0.46         ((k7_funcop_1 @ X9 @ X10) = (k2_funcop_1 @ X9 @ X10))),
% 0.19/0.46      inference('cnf', [status(esa)], [redefinition_k7_funcop_1])).
% 0.19/0.46  thf('14', plain,
% 0.19/0.46      (![X4 : $i, X6 : $i]: (v4_relat_1 @ (k7_funcop_1 @ X4 @ X6) @ X4)),
% 0.19/0.46      inference('demod', [status(thm)], ['12', '13'])).
% 0.19/0.46  thf('15', plain,
% 0.19/0.46      (![X4 : $i, X7 : $i]: (v1_funct_1 @ (k2_funcop_1 @ X4 @ X7))),
% 0.19/0.46      inference('cnf', [status(esa)], [fc20_funcop_1])).
% 0.19/0.46  thf('16', plain,
% 0.19/0.46      (![X9 : $i, X10 : $i]:
% 0.19/0.46         ((k7_funcop_1 @ X9 @ X10) = (k2_funcop_1 @ X9 @ X10))),
% 0.19/0.46      inference('cnf', [status(esa)], [redefinition_k7_funcop_1])).
% 0.19/0.46  thf('17', plain,
% 0.19/0.46      (![X4 : $i, X7 : $i]: (v1_funct_1 @ (k7_funcop_1 @ X4 @ X7))),
% 0.19/0.46      inference('demod', [status(thm)], ['15', '16'])).
% 0.19/0.46  thf('18', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (~ (v1_yellow_1 @ (k7_funcop_1 @ k1_xboole_0 @ X0))
% 0.19/0.46          | ((k5_yellow_1 @ k1_xboole_0 @ (k7_funcop_1 @ k1_xboole_0 @ X0))
% 0.19/0.46              = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.19/0.46                 (k6_partfun1 @ (k1_tarski @ k1_xboole_0)))))),
% 0.19/0.46      inference('demod', [status(thm)], ['8', '11', '14', '17'])).
% 0.19/0.46  thf('19', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (~ (l1_orders_2 @ X0)
% 0.19/0.46          | ((k5_yellow_1 @ k1_xboole_0 @ (k7_funcop_1 @ k1_xboole_0 @ X0))
% 0.19/0.46              = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.19/0.46                 (k6_partfun1 @ (k1_tarski @ k1_xboole_0)))))),
% 0.19/0.46      inference('sup-', [status(thm)], ['3', '18'])).
% 0.19/0.46  thf('20', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (((k6_yellow_1 @ k1_xboole_0 @ X0)
% 0.19/0.46            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.19/0.46               (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))
% 0.19/0.46          | ~ (l1_orders_2 @ X0)
% 0.19/0.46          | ~ (l1_orders_2 @ X0))),
% 0.19/0.46      inference('sup+', [status(thm)], ['0', '19'])).
% 0.19/0.46  thf('21', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (~ (l1_orders_2 @ X0)
% 0.19/0.46          | ((k6_yellow_1 @ k1_xboole_0 @ X0)
% 0.19/0.46              = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.19/0.46                 (k6_partfun1 @ (k1_tarski @ k1_xboole_0)))))),
% 0.19/0.46      inference('simplify', [status(thm)], ['20'])).
% 0.19/0.46  thf(t27_yellow_1, conjecture,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( l1_orders_2 @ A ) =>
% 0.19/0.46       ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 0.19/0.46         ( g1_orders_2 @
% 0.19/0.46           ( k1_tarski @ k1_xboole_0 ) @ 
% 0.19/0.46           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i]:
% 0.19/0.46        ( ( l1_orders_2 @ A ) =>
% 0.19/0.46          ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 0.19/0.46            ( g1_orders_2 @
% 0.19/0.46              ( k1_tarski @ k1_xboole_0 ) @ 
% 0.19/0.46              ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t27_yellow_1])).
% 0.19/0.46  thf('22', plain,
% 0.19/0.46      (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.19/0.46         != (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.19/0.46             (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('23', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.19/0.46            != (k6_yellow_1 @ k1_xboole_0 @ X0))
% 0.19/0.46          | ~ (l1_orders_2 @ X0))),
% 0.19/0.46      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.46  thf('24', plain, (~ (l1_orders_2 @ sk_A)),
% 0.19/0.46      inference('eq_res', [status(thm)], ['23'])).
% 0.19/0.46  thf('25', plain, ((l1_orders_2 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('26', plain, ($false), inference('demod', [status(thm)], ['24', '25'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
