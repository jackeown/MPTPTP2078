%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Q7SpQfeIFD

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:18 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   59 (  82 expanded)
%              Number of leaves         :   22 (  33 expanded)
%              Depth                    :   14
%              Number of atoms          :  426 ( 743 expanded)
%              Number of equality atoms :   19 (  32 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t50_subset_1,conjecture,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ( ~ ( r2_hidden @ C @ B )
               => ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( A != k1_xboole_0 )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ A )
               => ( ~ ( r2_hidden @ C @ B )
                 => ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X51 @ X52 )
      | ( r2_hidden @ X51 @ X52 )
      | ( v1_xboole_0 @ X52 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ( r2_hidden @ X8 @ ( k5_xboole_0 @ X9 @ X11 ) )
      | ( r2_hidden @ X8 @ X11 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ sk_C @ X0 )
      | ( r2_hidden @ sk_C @ ( k5_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ sk_C @ X0 )
      | ( r2_hidden @ sk_C @ ( k5_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_C @ ( k4_xboole_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ sk_C @ ( k3_xboole_0 @ sk_A @ X0 ) )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('14',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('16',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X10 )
      | ~ ( r2_hidden @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X3 @ X0 )
      | ~ ( r2_hidden @ X3 @ ( k5_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( k4_xboole_0 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ sk_C @ ( k2_xboole_0 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ sk_C @ ( k5_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ sk_C @ ( k5_xboole_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ sk_C @ ( k4_xboole_0 @ sk_A @ X0 ) )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_C @ ( k4_xboole_0 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ sk_C @ ( k5_xboole_0 @ sk_A @ X0 ) )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_C @ X0 )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_C @ ( k4_xboole_0 @ sk_A @ X0 ) )
      | ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ sk_C @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ~ ( r2_hidden @ sk_C @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X54: $i,X55: $i] :
      ( ( ( k3_subset_1 @ X54 @ X55 )
        = ( k4_xboole_0 @ X54 @ X55 ) )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('27',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( r2_hidden @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,
    ( ( r2_hidden @ sk_C @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    ~ ( r2_hidden @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['29','30'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('32',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('33',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Q7SpQfeIFD
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:47:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.49/1.75  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.49/1.75  % Solved by: fo/fo7.sh
% 1.49/1.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.49/1.75  % done 1545 iterations in 1.288s
% 1.49/1.75  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.49/1.75  % SZS output start Refutation
% 1.49/1.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.49/1.75  thf(sk_C_type, type, sk_C: $i).
% 1.49/1.75  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.49/1.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.49/1.75  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.49/1.75  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.49/1.75  thf(sk_A_type, type, sk_A: $i).
% 1.49/1.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.49/1.75  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.49/1.75  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.49/1.75  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.49/1.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.49/1.75  thf(sk_B_type, type, sk_B: $i).
% 1.49/1.75  thf(t50_subset_1, conjecture,
% 1.49/1.75    (![A:$i]:
% 1.49/1.75     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 1.49/1.75       ( ![B:$i]:
% 1.49/1.75         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.49/1.75           ( ![C:$i]:
% 1.49/1.75             ( ( m1_subset_1 @ C @ A ) =>
% 1.49/1.75               ( ( ~( r2_hidden @ C @ B ) ) =>
% 1.49/1.75                 ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) ) ))).
% 1.49/1.75  thf(zf_stmt_0, negated_conjecture,
% 1.49/1.75    (~( ![A:$i]:
% 1.49/1.75        ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 1.49/1.75          ( ![B:$i]:
% 1.49/1.75            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.49/1.75              ( ![C:$i]:
% 1.49/1.75                ( ( m1_subset_1 @ C @ A ) =>
% 1.49/1.75                  ( ( ~( r2_hidden @ C @ B ) ) =>
% 1.49/1.75                    ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) ) ) )),
% 1.49/1.75    inference('cnf.neg', [status(esa)], [t50_subset_1])).
% 1.49/1.75  thf('0', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 1.49/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.75  thf(d2_subset_1, axiom,
% 1.49/1.75    (![A:$i,B:$i]:
% 1.49/1.75     ( ( ( v1_xboole_0 @ A ) =>
% 1.49/1.75         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.49/1.75       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.49/1.75         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.49/1.75  thf('1', plain,
% 1.49/1.75      (![X51 : $i, X52 : $i]:
% 1.49/1.75         (~ (m1_subset_1 @ X51 @ X52)
% 1.49/1.75          | (r2_hidden @ X51 @ X52)
% 1.49/1.75          | (v1_xboole_0 @ X52))),
% 1.49/1.75      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.49/1.75  thf('2', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_C @ sk_A))),
% 1.49/1.75      inference('sup-', [status(thm)], ['0', '1'])).
% 1.49/1.75  thf(t1_xboole_0, axiom,
% 1.49/1.75    (![A:$i,B:$i,C:$i]:
% 1.49/1.75     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 1.49/1.75       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 1.49/1.75  thf('3', plain,
% 1.49/1.75      (![X8 : $i, X9 : $i, X11 : $i]:
% 1.49/1.75         ((r2_hidden @ X8 @ (k5_xboole_0 @ X9 @ X11))
% 1.49/1.75          | (r2_hidden @ X8 @ X11)
% 1.49/1.75          | ~ (r2_hidden @ X8 @ X9))),
% 1.49/1.75      inference('cnf', [status(esa)], [t1_xboole_0])).
% 1.49/1.75  thf('4', plain,
% 1.49/1.75      (![X0 : $i]:
% 1.49/1.75         ((v1_xboole_0 @ sk_A)
% 1.49/1.75          | (r2_hidden @ sk_C @ X0)
% 1.49/1.75          | (r2_hidden @ sk_C @ (k5_xboole_0 @ sk_A @ X0)))),
% 1.49/1.75      inference('sup-', [status(thm)], ['2', '3'])).
% 1.49/1.75  thf('5', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_C @ sk_A))),
% 1.49/1.75      inference('sup-', [status(thm)], ['0', '1'])).
% 1.49/1.75  thf(d3_xboole_0, axiom,
% 1.49/1.75    (![A:$i,B:$i,C:$i]:
% 1.49/1.75     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 1.49/1.75       ( ![D:$i]:
% 1.49/1.75         ( ( r2_hidden @ D @ C ) <=>
% 1.49/1.75           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.49/1.75  thf('6', plain,
% 1.49/1.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.49/1.75         (~ (r2_hidden @ X0 @ X3)
% 1.49/1.75          | (r2_hidden @ X0 @ X2)
% 1.49/1.75          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 1.49/1.75      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.49/1.75  thf('7', plain,
% 1.49/1.75      (![X0 : $i, X1 : $i, X3 : $i]:
% 1.49/1.75         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 1.49/1.75      inference('simplify', [status(thm)], ['6'])).
% 1.49/1.75  thf('8', plain,
% 1.49/1.75      (![X0 : $i]:
% 1.49/1.75         ((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_C @ (k2_xboole_0 @ sk_A @ X0)))),
% 1.49/1.75      inference('sup-', [status(thm)], ['5', '7'])).
% 1.49/1.75  thf(t100_xboole_1, axiom,
% 1.49/1.75    (![A:$i,B:$i]:
% 1.49/1.75     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.49/1.75  thf('9', plain,
% 1.49/1.75      (![X12 : $i, X13 : $i]:
% 1.49/1.75         ((k4_xboole_0 @ X12 @ X13)
% 1.49/1.75           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 1.49/1.75      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.49/1.75  thf('10', plain,
% 1.49/1.75      (![X0 : $i]:
% 1.49/1.75         ((v1_xboole_0 @ sk_A)
% 1.49/1.75          | (r2_hidden @ sk_C @ X0)
% 1.49/1.75          | (r2_hidden @ sk_C @ (k5_xboole_0 @ sk_A @ X0)))),
% 1.49/1.75      inference('sup-', [status(thm)], ['2', '3'])).
% 1.49/1.75  thf('11', plain,
% 1.49/1.75      (![X0 : $i]:
% 1.49/1.75         ((r2_hidden @ sk_C @ (k4_xboole_0 @ sk_A @ X0))
% 1.49/1.75          | (r2_hidden @ sk_C @ (k3_xboole_0 @ sk_A @ X0))
% 1.49/1.75          | (v1_xboole_0 @ sk_A))),
% 1.49/1.75      inference('sup+', [status(thm)], ['9', '10'])).
% 1.49/1.75  thf(t95_xboole_1, axiom,
% 1.49/1.75    (![A:$i,B:$i]:
% 1.49/1.75     ( ( k3_xboole_0 @ A @ B ) =
% 1.49/1.75       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 1.49/1.75  thf('12', plain,
% 1.49/1.75      (![X18 : $i, X19 : $i]:
% 1.49/1.75         ((k3_xboole_0 @ X18 @ X19)
% 1.49/1.75           = (k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ 
% 1.49/1.75              (k2_xboole_0 @ X18 @ X19)))),
% 1.49/1.75      inference('cnf', [status(esa)], [t95_xboole_1])).
% 1.49/1.75  thf(t91_xboole_1, axiom,
% 1.49/1.75    (![A:$i,B:$i,C:$i]:
% 1.49/1.75     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.49/1.75       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.49/1.75  thf('13', plain,
% 1.49/1.75      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.49/1.75         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 1.49/1.75           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 1.49/1.75      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.49/1.75  thf('14', plain,
% 1.49/1.75      (![X18 : $i, X19 : $i]:
% 1.49/1.75         ((k3_xboole_0 @ X18 @ X19)
% 1.49/1.75           = (k5_xboole_0 @ X18 @ 
% 1.49/1.75              (k5_xboole_0 @ X19 @ (k2_xboole_0 @ X18 @ X19))))),
% 1.49/1.75      inference('demod', [status(thm)], ['12', '13'])).
% 1.49/1.75  thf('15', plain,
% 1.49/1.75      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.49/1.75         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 1.49/1.75           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 1.49/1.75      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.49/1.75  thf('16', plain,
% 1.49/1.75      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.49/1.75         (~ (r2_hidden @ X8 @ X9)
% 1.49/1.75          | ~ (r2_hidden @ X8 @ X10)
% 1.49/1.75          | ~ (r2_hidden @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 1.49/1.75      inference('cnf', [status(esa)], [t1_xboole_0])).
% 1.49/1.75  thf('17', plain,
% 1.49/1.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.49/1.75         (~ (r2_hidden @ X3 @ (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))
% 1.49/1.75          | ~ (r2_hidden @ X3 @ X0)
% 1.49/1.75          | ~ (r2_hidden @ X3 @ (k5_xboole_0 @ X2 @ X1)))),
% 1.49/1.75      inference('sup-', [status(thm)], ['15', '16'])).
% 1.49/1.75  thf('18', plain,
% 1.49/1.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.49/1.75         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.49/1.75          | ~ (r2_hidden @ X2 @ (k5_xboole_0 @ X1 @ X0))
% 1.49/1.75          | ~ (r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.49/1.75      inference('sup-', [status(thm)], ['14', '17'])).
% 1.49/1.75  thf('19', plain,
% 1.49/1.75      (![X0 : $i]:
% 1.49/1.75         ((v1_xboole_0 @ sk_A)
% 1.49/1.75          | (r2_hidden @ sk_C @ (k4_xboole_0 @ sk_A @ X0))
% 1.49/1.75          | ~ (r2_hidden @ sk_C @ (k2_xboole_0 @ sk_A @ X0))
% 1.49/1.75          | ~ (r2_hidden @ sk_C @ (k5_xboole_0 @ sk_A @ X0)))),
% 1.49/1.75      inference('sup-', [status(thm)], ['11', '18'])).
% 1.49/1.75  thf('20', plain,
% 1.49/1.75      (![X0 : $i]:
% 1.49/1.75         ((v1_xboole_0 @ sk_A)
% 1.49/1.75          | ~ (r2_hidden @ sk_C @ (k5_xboole_0 @ sk_A @ X0))
% 1.49/1.75          | (r2_hidden @ sk_C @ (k4_xboole_0 @ sk_A @ X0))
% 1.49/1.75          | (v1_xboole_0 @ sk_A))),
% 1.49/1.75      inference('sup-', [status(thm)], ['8', '19'])).
% 1.49/1.75  thf('21', plain,
% 1.49/1.75      (![X0 : $i]:
% 1.49/1.75         ((r2_hidden @ sk_C @ (k4_xboole_0 @ sk_A @ X0))
% 1.49/1.75          | ~ (r2_hidden @ sk_C @ (k5_xboole_0 @ sk_A @ X0))
% 1.49/1.75          | (v1_xboole_0 @ sk_A))),
% 1.49/1.75      inference('simplify', [status(thm)], ['20'])).
% 1.49/1.75  thf('22', plain,
% 1.49/1.75      (![X0 : $i]:
% 1.49/1.75         ((r2_hidden @ sk_C @ X0)
% 1.49/1.75          | (v1_xboole_0 @ sk_A)
% 1.49/1.75          | (v1_xboole_0 @ sk_A)
% 1.49/1.75          | (r2_hidden @ sk_C @ (k4_xboole_0 @ sk_A @ X0)))),
% 1.49/1.75      inference('sup-', [status(thm)], ['4', '21'])).
% 1.49/1.75  thf('23', plain,
% 1.49/1.75      (![X0 : $i]:
% 1.49/1.75         ((r2_hidden @ sk_C @ (k4_xboole_0 @ sk_A @ X0))
% 1.49/1.75          | (v1_xboole_0 @ sk_A)
% 1.49/1.75          | (r2_hidden @ sk_C @ X0))),
% 1.49/1.75      inference('simplify', [status(thm)], ['22'])).
% 1.49/1.75  thf('24', plain, (~ (r2_hidden @ sk_C @ (k3_subset_1 @ sk_A @ sk_B))),
% 1.49/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.75  thf('25', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.49/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.75  thf(d5_subset_1, axiom,
% 1.49/1.75    (![A:$i,B:$i]:
% 1.49/1.75     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.49/1.75       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.49/1.75  thf('26', plain,
% 1.49/1.75      (![X54 : $i, X55 : $i]:
% 1.49/1.75         (((k3_subset_1 @ X54 @ X55) = (k4_xboole_0 @ X54 @ X55))
% 1.49/1.75          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ X54)))),
% 1.49/1.75      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.49/1.75  thf('27', plain,
% 1.49/1.75      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 1.49/1.75      inference('sup-', [status(thm)], ['25', '26'])).
% 1.49/1.75  thf('28', plain, (~ (r2_hidden @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B))),
% 1.49/1.75      inference('demod', [status(thm)], ['24', '27'])).
% 1.49/1.75  thf('29', plain, (((r2_hidden @ sk_C @ sk_B) | (v1_xboole_0 @ sk_A))),
% 1.49/1.75      inference('sup-', [status(thm)], ['23', '28'])).
% 1.49/1.75  thf('30', plain, (~ (r2_hidden @ sk_C @ sk_B)),
% 1.49/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.75  thf('31', plain, ((v1_xboole_0 @ sk_A)),
% 1.49/1.75      inference('clc', [status(thm)], ['29', '30'])).
% 1.49/1.75  thf(l13_xboole_0, axiom,
% 1.49/1.75    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.49/1.75  thf('32', plain,
% 1.49/1.75      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 1.49/1.75      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.49/1.75  thf('33', plain, (((sk_A) = (k1_xboole_0))),
% 1.49/1.75      inference('sup-', [status(thm)], ['31', '32'])).
% 1.49/1.75  thf('34', plain, (((sk_A) != (k1_xboole_0))),
% 1.49/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.75  thf('35', plain, ($false),
% 1.49/1.75      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 1.49/1.75  
% 1.49/1.75  % SZS output end Refutation
% 1.49/1.75  
% 1.49/1.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
