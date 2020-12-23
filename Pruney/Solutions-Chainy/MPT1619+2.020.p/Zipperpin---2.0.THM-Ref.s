%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7T2NhdfRKV

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:26 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 192 expanded)
%              Number of leaves         :   28 (  85 expanded)
%              Depth                    :   11
%              Number of atoms          :  380 (1415 expanded)
%              Number of equality atoms :   33 (  68 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_yellow_1_type,type,(
    k6_yellow_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k7_funcop_1_type,type,(
    k7_funcop_1: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k2_funcop_1_type,type,(
    k2_funcop_1: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(v1_yellow_1_type,type,(
    v1_yellow_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_yellow_1_type,type,(
    k5_yellow_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d5_yellow_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ B )
     => ( ( k6_yellow_1 @ A @ B )
        = ( k5_yellow_1 @ A @ ( k7_funcop_1 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k6_yellow_1 @ X14 @ X15 )
        = ( k5_yellow_1 @ X14 @ ( k7_funcop_1 @ X14 @ X15 ) ) )
      | ~ ( l1_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d5_yellow_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

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
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

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

thf('4',plain,(
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
 != ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(rc1_yellow_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v1_yellow_1 @ B )
      & ( v1_partfun1 @ B @ A )
      & ( v1_funct_1 @ B )
      & ( v4_relat_1 @ B @ A )
      & ( v1_relat_1 @ B ) ) )).

thf('5',plain,(
    ! [X19: $i] :
      ( v1_partfun1 @ ( sk_B_2 @ X19 ) @ X19 ) ),
    inference(cnf,[status(esa)],[rc1_yellow_1])).

thf(t26_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v4_relat_1 @ A @ k1_xboole_0 )
        & ( v1_funct_1 @ A )
        & ( v1_partfun1 @ A @ k1_xboole_0 )
        & ( v1_yellow_1 @ A ) )
     => ( ( k5_yellow_1 @ k1_xboole_0 @ A )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) )).

thf('6',plain,(
    ! [X23: $i] :
      ( ( ( k5_yellow_1 @ k1_xboole_0 @ X23 )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) )
      | ~ ( v1_yellow_1 @ X23 )
      | ~ ( v1_partfun1 @ X23 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v4_relat_1 @ X23 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t26_yellow_1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ ( sk_B_2 @ k1_xboole_0 ) )
    | ~ ( v4_relat_1 @ ( sk_B_2 @ k1_xboole_0 ) @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ ( sk_B_2 @ k1_xboole_0 ) )
    | ~ ( v1_yellow_1 @ ( sk_B_2 @ k1_xboole_0 ) )
    | ( ( k5_yellow_1 @ k1_xboole_0 @ ( sk_B_2 @ k1_xboole_0 ) )
      = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X19: $i] :
      ( v1_partfun1 @ ( sk_B_2 @ X19 ) @ X19 ) ),
    inference(cnf,[status(esa)],[rc1_yellow_1])).

thf(t134_pboole,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v4_relat_1 @ A @ k1_xboole_0 )
        & ( v1_funct_1 @ A )
        & ( v1_partfun1 @ A @ k1_xboole_0 ) )
     => ( A = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X22: $i] :
      ( ( X22 = k1_xboole_0 )
      | ~ ( v1_partfun1 @ X22 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v4_relat_1 @ X22 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t134_pboole])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ ( sk_B_2 @ k1_xboole_0 ) )
    | ~ ( v4_relat_1 @ ( sk_B_2 @ k1_xboole_0 ) @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ ( sk_B_2 @ k1_xboole_0 ) )
    | ( ( sk_B_2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( sk_B_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[rc1_yellow_1])).

thf('12',plain,(
    ! [X19: $i] :
      ( v4_relat_1 @ ( sk_B_2 @ X19 ) @ X19 ) ),
    inference(cnf,[status(esa)],[rc1_yellow_1])).

thf('13',plain,(
    ! [X19: $i] :
      ( v1_funct_1 @ ( sk_B_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[rc1_yellow_1])).

thf('14',plain,
    ( ( sk_B_2 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('15',plain,
    ( ( sk_B_2 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('16',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( sk_B_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[rc1_yellow_1])).

thf('17',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_B_2 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('19',plain,
    ( ( sk_B_2 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('20',plain,(
    ! [X19: $i] :
      ( v4_relat_1 @ ( sk_B_2 @ X19 ) @ X19 ) ),
    inference(cnf,[status(esa)],[rc1_yellow_1])).

thf('21',plain,(
    v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_B_2 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('23',plain,
    ( ( sk_B_2 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('24',plain,(
    ! [X19: $i] :
      ( v1_funct_1 @ ( sk_B_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[rc1_yellow_1])).

thf('25',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_B_2 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('27',plain,
    ( ( sk_B_2 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('28',plain,(
    ! [X19: $i] :
      ( v1_yellow_1 @ ( sk_B_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[rc1_yellow_1])).

thf('29',plain,(
    v1_yellow_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_B_2 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('31',plain,
    ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
    = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['7','14','17','18','21','22','25','26','29','30'])).

thf('32',plain,(
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
 != ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
       != ( k5_yellow_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
       != ( k6_yellow_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_xboole_0 @ ( k7_funcop_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','33'])).

thf(fc2_funcop_1,axiom,(
    ! [A: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ A ) ) )).

thf('35',plain,(
    ! [X18: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc2_funcop_1])).

thf(redefinition_k7_funcop_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k7_funcop_1 @ A @ B )
      = ( k2_funcop_1 @ A @ B ) ) )).

thf('36',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k7_funcop_1 @ X20 @ X21 )
      = ( k2_funcop_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_funcop_1])).

thf('37',plain,(
    ! [X18: $i] :
      ( v1_xboole_0 @ ( k7_funcop_1 @ k1_xboole_0 @ X18 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k7_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X18: $i] :
      ( v1_xboole_0 @ ( k7_funcop_1 @ k1_xboole_0 @ X18 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k7_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
       != ( k6_yellow_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','39','42'])).

thf('44',plain,(
    ~ ( l1_orders_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['43'])).

thf('45',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['44','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7T2NhdfRKV
% 0.15/0.36  % Computer   : n021.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 15:34:34 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 40 iterations in 0.023s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.50  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.22/0.50  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(k6_yellow_1_type, type, k6_yellow_1: $i > $i > $i).
% 0.22/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.50  thf(k7_funcop_1_type, type, k7_funcop_1: $i > $i > $i).
% 0.22/0.50  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.22/0.50  thf(k2_funcop_1_type, type, k2_funcop_1: $i > $i > $i).
% 0.22/0.50  thf(sk_B_2_type, type, sk_B_2: $i > $i).
% 0.22/0.50  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.22/0.50  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 0.22/0.50  thf(v1_yellow_1_type, type, v1_yellow_1: $i > $o).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(k5_yellow_1_type, type, k5_yellow_1: $i > $i > $i).
% 0.22/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.50  thf(d5_yellow_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( l1_orders_2 @ B ) =>
% 0.22/0.50       ( ( k6_yellow_1 @ A @ B ) =
% 0.22/0.50         ( k5_yellow_1 @ A @ ( k7_funcop_1 @ A @ B ) ) ) ))).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      (![X14 : $i, X15 : $i]:
% 0.22/0.50         (((k6_yellow_1 @ X14 @ X15)
% 0.22/0.50            = (k5_yellow_1 @ X14 @ (k7_funcop_1 @ X14 @ X15)))
% 0.22/0.50          | ~ (l1_orders_2 @ X15))),
% 0.22/0.50      inference('cnf', [status(esa)], [d5_yellow_1])).
% 0.22/0.50  thf(t7_xboole_0, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.50          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X3) @ X3))),
% 0.22/0.50      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.22/0.50  thf(d1_xboole_0, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.22/0.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.50  thf(t27_yellow_1, conjecture,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l1_orders_2 @ A ) =>
% 0.22/0.50       ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 0.22/0.50         ( g1_orders_2 @
% 0.22/0.50           ( k1_tarski @ k1_xboole_0 ) @ 
% 0.22/0.50           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i]:
% 0.22/0.50        ( ( l1_orders_2 @ A ) =>
% 0.22/0.50          ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 0.22/0.50            ( g1_orders_2 @
% 0.22/0.50              ( k1_tarski @ k1_xboole_0 ) @ 
% 0.22/0.50              ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t27_yellow_1])).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.22/0.50         != (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.22/0.50             (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(rc1_yellow_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ?[B:$i]:
% 0.22/0.50       ( ( v1_yellow_1 @ B ) & ( v1_partfun1 @ B @ A ) & ( v1_funct_1 @ B ) & 
% 0.22/0.50         ( v4_relat_1 @ B @ A ) & ( v1_relat_1 @ B ) ) ))).
% 0.22/0.50  thf('5', plain, (![X19 : $i]: (v1_partfun1 @ (sk_B_2 @ X19) @ X19)),
% 0.22/0.50      inference('cnf', [status(esa)], [rc1_yellow_1])).
% 0.22/0.50  thf(t26_yellow_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( v1_relat_1 @ A ) & ( v4_relat_1 @ A @ k1_xboole_0 ) & 
% 0.22/0.50         ( v1_funct_1 @ A ) & ( v1_partfun1 @ A @ k1_xboole_0 ) & 
% 0.22/0.50         ( v1_yellow_1 @ A ) ) =>
% 0.22/0.50       ( ( k5_yellow_1 @ k1_xboole_0 @ A ) =
% 0.22/0.50         ( g1_orders_2 @
% 0.22/0.50           ( k1_tarski @ k1_xboole_0 ) @ 
% 0.22/0.50           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (![X23 : $i]:
% 0.22/0.50         (((k5_yellow_1 @ k1_xboole_0 @ X23)
% 0.22/0.50            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.22/0.50               (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))
% 0.22/0.50          | ~ (v1_yellow_1 @ X23)
% 0.22/0.50          | ~ (v1_partfun1 @ X23 @ k1_xboole_0)
% 0.22/0.50          | ~ (v1_funct_1 @ X23)
% 0.22/0.50          | ~ (v4_relat_1 @ X23 @ k1_xboole_0)
% 0.22/0.50          | ~ (v1_relat_1 @ X23))),
% 0.22/0.50      inference('cnf', [status(esa)], [t26_yellow_1])).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      ((~ (v1_relat_1 @ (sk_B_2 @ k1_xboole_0))
% 0.22/0.50        | ~ (v4_relat_1 @ (sk_B_2 @ k1_xboole_0) @ k1_xboole_0)
% 0.22/0.50        | ~ (v1_funct_1 @ (sk_B_2 @ k1_xboole_0))
% 0.22/0.50        | ~ (v1_yellow_1 @ (sk_B_2 @ k1_xboole_0))
% 0.22/0.50        | ((k5_yellow_1 @ k1_xboole_0 @ (sk_B_2 @ k1_xboole_0))
% 0.22/0.50            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.22/0.50               (k6_partfun1 @ (k1_tarski @ k1_xboole_0)))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.50  thf('8', plain, (![X19 : $i]: (v1_partfun1 @ (sk_B_2 @ X19) @ X19)),
% 0.22/0.50      inference('cnf', [status(esa)], [rc1_yellow_1])).
% 0.22/0.50  thf(t134_pboole, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( v1_relat_1 @ A ) & ( v4_relat_1 @ A @ k1_xboole_0 ) & 
% 0.22/0.50         ( v1_funct_1 @ A ) & ( v1_partfun1 @ A @ k1_xboole_0 ) ) =>
% 0.22/0.50       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      (![X22 : $i]:
% 0.22/0.50         (((X22) = (k1_xboole_0))
% 0.22/0.50          | ~ (v1_partfun1 @ X22 @ k1_xboole_0)
% 0.22/0.50          | ~ (v1_funct_1 @ X22)
% 0.22/0.50          | ~ (v4_relat_1 @ X22 @ k1_xboole_0)
% 0.22/0.50          | ~ (v1_relat_1 @ X22))),
% 0.22/0.50      inference('cnf', [status(esa)], [t134_pboole])).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      ((~ (v1_relat_1 @ (sk_B_2 @ k1_xboole_0))
% 0.22/0.50        | ~ (v4_relat_1 @ (sk_B_2 @ k1_xboole_0) @ k1_xboole_0)
% 0.22/0.50        | ~ (v1_funct_1 @ (sk_B_2 @ k1_xboole_0))
% 0.22/0.50        | ((sk_B_2 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.50  thf('11', plain, (![X19 : $i]: (v1_relat_1 @ (sk_B_2 @ X19))),
% 0.22/0.50      inference('cnf', [status(esa)], [rc1_yellow_1])).
% 0.22/0.50  thf('12', plain, (![X19 : $i]: (v4_relat_1 @ (sk_B_2 @ X19) @ X19)),
% 0.22/0.50      inference('cnf', [status(esa)], [rc1_yellow_1])).
% 0.22/0.50  thf('13', plain, (![X19 : $i]: (v1_funct_1 @ (sk_B_2 @ X19))),
% 0.22/0.50      inference('cnf', [status(esa)], [rc1_yellow_1])).
% 0.22/0.50  thf('14', plain, (((sk_B_2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.22/0.50  thf('15', plain, (((sk_B_2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.22/0.50  thf('16', plain, (![X19 : $i]: (v1_relat_1 @ (sk_B_2 @ X19))),
% 0.22/0.50      inference('cnf', [status(esa)], [rc1_yellow_1])).
% 0.22/0.50  thf('17', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.50      inference('sup+', [status(thm)], ['15', '16'])).
% 0.22/0.50  thf('18', plain, (((sk_B_2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.22/0.50  thf('19', plain, (((sk_B_2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.22/0.50  thf('20', plain, (![X19 : $i]: (v4_relat_1 @ (sk_B_2 @ X19) @ X19)),
% 0.22/0.50      inference('cnf', [status(esa)], [rc1_yellow_1])).
% 0.22/0.50  thf('21', plain, ((v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.22/0.50      inference('sup+', [status(thm)], ['19', '20'])).
% 0.22/0.50  thf('22', plain, (((sk_B_2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.22/0.50  thf('23', plain, (((sk_B_2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.22/0.50  thf('24', plain, (![X19 : $i]: (v1_funct_1 @ (sk_B_2 @ X19))),
% 0.22/0.50      inference('cnf', [status(esa)], [rc1_yellow_1])).
% 0.22/0.50  thf('25', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.22/0.50      inference('sup+', [status(thm)], ['23', '24'])).
% 0.22/0.50  thf('26', plain, (((sk_B_2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.22/0.50  thf('27', plain, (((sk_B_2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.22/0.50  thf('28', plain, (![X19 : $i]: (v1_yellow_1 @ (sk_B_2 @ X19))),
% 0.22/0.50      inference('cnf', [status(esa)], [rc1_yellow_1])).
% 0.22/0.50  thf('29', plain, ((v1_yellow_1 @ k1_xboole_0)),
% 0.22/0.50      inference('sup+', [status(thm)], ['27', '28'])).
% 0.22/0.50  thf('30', plain, (((sk_B_2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.22/0.50  thf('31', plain,
% 0.22/0.50      (((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.22/0.50         = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.22/0.50            (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))),
% 0.22/0.50      inference('demod', [status(thm)],
% 0.22/0.50                ['7', '14', '17', '18', '21', '22', '25', '26', '29', '30'])).
% 0.22/0.50  thf('32', plain,
% 0.22/0.50      (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.22/0.50         != (k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0))),
% 0.22/0.50      inference('demod', [status(thm)], ['4', '31'])).
% 0.22/0.50  thf('33', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.22/0.50            != (k5_yellow_1 @ k1_xboole_0 @ X0))
% 0.22/0.50          | ~ (v1_xboole_0 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['3', '32'])).
% 0.22/0.50  thf('34', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.22/0.50            != (k6_yellow_1 @ k1_xboole_0 @ X0))
% 0.22/0.50          | ~ (l1_orders_2 @ X0)
% 0.22/0.50          | ~ (v1_xboole_0 @ (k7_funcop_1 @ k1_xboole_0 @ X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['0', '33'])).
% 0.22/0.50  thf(fc2_funcop_1, axiom,
% 0.22/0.50    (![A:$i]: ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ A ) ))).
% 0.22/0.50  thf('35', plain,
% 0.22/0.50      (![X18 : $i]: (v1_xboole_0 @ (k2_funcop_1 @ k1_xboole_0 @ X18))),
% 0.22/0.50      inference('cnf', [status(esa)], [fc2_funcop_1])).
% 0.22/0.50  thf(redefinition_k7_funcop_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]: ( ( k7_funcop_1 @ A @ B ) = ( k2_funcop_1 @ A @ B ) ))).
% 0.22/0.50  thf('36', plain,
% 0.22/0.50      (![X20 : $i, X21 : $i]:
% 0.22/0.50         ((k7_funcop_1 @ X20 @ X21) = (k2_funcop_1 @ X20 @ X21))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k7_funcop_1])).
% 0.22/0.50  thf('37', plain,
% 0.22/0.50      (![X18 : $i]: (v1_xboole_0 @ (k7_funcop_1 @ k1_xboole_0 @ X18))),
% 0.22/0.50      inference('demod', [status(thm)], ['35', '36'])).
% 0.22/0.50  thf('38', plain,
% 0.22/0.50      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.50  thf('39', plain,
% 0.22/0.50      (![X0 : $i]: ((k7_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.50  thf('40', plain,
% 0.22/0.50      (![X18 : $i]: (v1_xboole_0 @ (k7_funcop_1 @ k1_xboole_0 @ X18))),
% 0.22/0.50      inference('demod', [status(thm)], ['35', '36'])).
% 0.22/0.50  thf('41', plain,
% 0.22/0.50      (![X0 : $i]: ((k7_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.50  thf('42', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.50      inference('demod', [status(thm)], ['40', '41'])).
% 0.22/0.50  thf('43', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.22/0.50            != (k6_yellow_1 @ k1_xboole_0 @ X0))
% 0.22/0.50          | ~ (l1_orders_2 @ X0))),
% 0.22/0.50      inference('demod', [status(thm)], ['34', '39', '42'])).
% 0.22/0.50  thf('44', plain, (~ (l1_orders_2 @ sk_A)),
% 0.22/0.50      inference('eq_res', [status(thm)], ['43'])).
% 0.22/0.50  thf('45', plain, ((l1_orders_2 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('46', plain, ($false), inference('demod', [status(thm)], ['44', '45'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
