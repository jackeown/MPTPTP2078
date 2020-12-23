%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2sEQG9A4yI

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   58 (  96 expanded)
%              Number of leaves         :   16 (  34 expanded)
%              Depth                    :   16
%              Number of atoms          :  476 (1176 expanded)
%              Number of equality atoms :   12 (  44 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_tsep_1_type,type,(
    k2_tsep_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('0',plain,(
    ! [X5: $i] :
      ( ( m1_pre_topc @ X5 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t26_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ( ( k2_tsep_1 @ A @ B @ B )
            = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ( ( k2_tsep_1 @ A @ B @ B )
              = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t26_tmap_1])).

thf('1',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t22_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( m1_pre_topc @ B @ C )
               => ( ~ ( r1_tsep_1 @ B @ C )
                  & ~ ( r1_tsep_1 @ C @ B ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X3 )
      | ~ ( m1_pre_topc @ X2 @ X4 )
      | ~ ( r1_tsep_1 @ X4 @ X2 )
      | ~ ( m1_pre_topc @ X4 @ X3 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t22_tmap_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tsep_1 @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tsep_1 @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( r1_tsep_1 @ sk_B @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X5: $i] :
      ( ( m1_pre_topc @ X5 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('11',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ~ ( r1_tsep_1 @ B @ C )
               => ( ( ( m1_pre_topc @ B @ C )
                   => ( ( k2_tsep_1 @ A @ B @ C )
                      = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) )
                  & ( ( ( k2_tsep_1 @ A @ B @ C )
                      = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                   => ( m1_pre_topc @ B @ C ) )
                  & ( ( m1_pre_topc @ C @ B )
                   => ( ( k2_tsep_1 @ A @ B @ C )
                      = ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) )
                  & ( ( ( k2_tsep_1 @ A @ B @ C )
                      = ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) )
                   => ( m1_pre_topc @ C @ B ) ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( m1_pre_topc @ X6 @ X7 )
      | ( r1_tsep_1 @ X6 @ X8 )
      | ~ ( m1_pre_topc @ X8 @ X6 )
      | ( ( k2_tsep_1 @ X7 @ X6 @ X8 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) ) )
      | ~ ( m1_pre_topc @ X8 @ X7 )
      | ( v2_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t31_tsep_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( k2_tsep_1 @ sk_A @ sk_B @ X0 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( k2_tsep_1 @ sk_A @ sk_B @ X0 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( ( k2_tsep_1 @ sk_A @ sk_B @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tsep_1 @ sk_A @ sk_B @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ( k2_tsep_1 @ sk_A @ sk_B @ sk_B )
 != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','21'])).

thf('23',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['22','27'])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tsep_1 @ sk_B @ sk_B ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    r1_tsep_1 @ sk_B @ sk_B ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['9','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_B ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ~ ( m1_pre_topc @ sk_B @ sk_B ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['0','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['25','26'])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['38','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2sEQG9A4yI
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:55:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 29 iterations in 0.022s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.49  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.22/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.49  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.22/0.49  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.22/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.49  thf(k2_tsep_1_type, type, k2_tsep_1: $i > $i > $i > $i).
% 0.22/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.49  thf(t2_tsep_1, axiom,
% 0.22/0.49    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      (![X5 : $i]: ((m1_pre_topc @ X5 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.22/0.49      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.22/0.49  thf(t26_tmap_1, conjecture,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.22/0.49           ( ( k2_tsep_1 @ A @ B @ B ) =
% 0.22/0.49             ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i]:
% 0.22/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.49            ( l1_pre_topc @ A ) ) =>
% 0.22/0.49          ( ![B:$i]:
% 0.22/0.49            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.22/0.49              ( ( k2_tsep_1 @ A @ B @ B ) =
% 0.22/0.49                ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t26_tmap_1])).
% 0.22/0.49  thf('1', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(t22_tmap_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.22/0.49           ( ![C:$i]:
% 0.22/0.49             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.49               ( ( m1_pre_topc @ B @ C ) =>
% 0.22/0.49                 ( ( ~( r1_tsep_1 @ B @ C ) ) & ( ~( r1_tsep_1 @ C @ B ) ) ) ) ) ) ) ) ))).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.49         ((v2_struct_0 @ X2)
% 0.22/0.49          | ~ (m1_pre_topc @ X2 @ X3)
% 0.22/0.49          | ~ (m1_pre_topc @ X2 @ X4)
% 0.22/0.49          | ~ (r1_tsep_1 @ X4 @ X2)
% 0.22/0.49          | ~ (m1_pre_topc @ X4 @ X3)
% 0.22/0.49          | (v2_struct_0 @ X4)
% 0.22/0.49          | ~ (l1_pre_topc @ X3)
% 0.22/0.49          | ~ (v2_pre_topc @ X3)
% 0.22/0.49          | (v2_struct_0 @ X3))),
% 0.22/0.49      inference('cnf', [status(esa)], [t22_tmap_1])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((v2_struct_0 @ sk_A)
% 0.22/0.49          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.49          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.49          | (v2_struct_0 @ X0)
% 0.22/0.49          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.22/0.49          | ~ (r1_tsep_1 @ X0 @ sk_B)
% 0.22/0.49          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.22/0.49          | (v2_struct_0 @ sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.49  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((v2_struct_0 @ sk_A)
% 0.22/0.49          | (v2_struct_0 @ X0)
% 0.22/0.49          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.22/0.49          | ~ (r1_tsep_1 @ X0 @ sk_B)
% 0.22/0.49          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.22/0.49          | (v2_struct_0 @ sk_B))),
% 0.22/0.49      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (((v2_struct_0 @ sk_B)
% 0.22/0.49        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 0.22/0.49        | ~ (r1_tsep_1 @ sk_B @ sk_B)
% 0.22/0.49        | (v2_struct_0 @ sk_B)
% 0.22/0.49        | (v2_struct_0 @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['1', '7'])).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      (((v2_struct_0 @ sk_A)
% 0.22/0.49        | ~ (r1_tsep_1 @ sk_B @ sk_B)
% 0.22/0.49        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 0.22/0.49        | (v2_struct_0 @ sk_B))),
% 0.22/0.49      inference('simplify', [status(thm)], ['8'])).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      (![X5 : $i]: ((m1_pre_topc @ X5 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.22/0.49      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.22/0.49  thf('11', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('12', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(t31_tsep_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.22/0.49           ( ![C:$i]:
% 0.22/0.49             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.49               ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 0.22/0.49                 ( ( ( m1_pre_topc @ B @ C ) =>
% 0.22/0.49                     ( ( k2_tsep_1 @ A @ B @ C ) =
% 0.22/0.49                       ( g1_pre_topc @
% 0.22/0.49                         ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) & 
% 0.22/0.49                   ( ( ( k2_tsep_1 @ A @ B @ C ) =
% 0.22/0.49                       ( g1_pre_topc @
% 0.22/0.49                         ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.22/0.49                     ( m1_pre_topc @ B @ C ) ) & 
% 0.22/0.49                   ( ( m1_pre_topc @ C @ B ) =>
% 0.22/0.49                     ( ( k2_tsep_1 @ A @ B @ C ) =
% 0.22/0.49                       ( g1_pre_topc @
% 0.22/0.49                         ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) ) & 
% 0.22/0.49                   ( ( ( k2_tsep_1 @ A @ B @ C ) =
% 0.22/0.49                       ( g1_pre_topc @
% 0.22/0.49                         ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) =>
% 0.22/0.49                     ( m1_pre_topc @ C @ B ) ) ) ) ) ) ) ) ))).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.49         ((v2_struct_0 @ X6)
% 0.22/0.49          | ~ (m1_pre_topc @ X6 @ X7)
% 0.22/0.49          | (r1_tsep_1 @ X6 @ X8)
% 0.22/0.49          | ~ (m1_pre_topc @ X8 @ X6)
% 0.22/0.49          | ((k2_tsep_1 @ X7 @ X6 @ X8)
% 0.22/0.49              = (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)))
% 0.22/0.49          | ~ (m1_pre_topc @ X8 @ X7)
% 0.22/0.49          | (v2_struct_0 @ X8)
% 0.22/0.49          | ~ (l1_pre_topc @ X7)
% 0.22/0.49          | ~ (v2_pre_topc @ X7)
% 0.22/0.49          | (v2_struct_0 @ X7))),
% 0.22/0.49      inference('cnf', [status(esa)], [t31_tsep_1])).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((v2_struct_0 @ sk_A)
% 0.22/0.49          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.49          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.49          | (v2_struct_0 @ X0)
% 0.22/0.49          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.22/0.49          | ((k2_tsep_1 @ sk_A @ sk_B @ X0)
% 0.22/0.49              = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.22/0.49          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.22/0.49          | (r1_tsep_1 @ sk_B @ X0)
% 0.22/0.49          | (v2_struct_0 @ sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.49  thf('15', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((v2_struct_0 @ sk_A)
% 0.22/0.49          | (v2_struct_0 @ X0)
% 0.22/0.49          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.22/0.49          | ((k2_tsep_1 @ sk_A @ sk_B @ X0)
% 0.22/0.49              = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.22/0.49          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.22/0.49          | (r1_tsep_1 @ sk_B @ X0)
% 0.22/0.49          | (v2_struct_0 @ sk_B))),
% 0.22/0.49      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      (((v2_struct_0 @ sk_B)
% 0.22/0.49        | (r1_tsep_1 @ sk_B @ sk_B)
% 0.22/0.49        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 0.22/0.49        | ((k2_tsep_1 @ sk_A @ sk_B @ sk_B)
% 0.22/0.49            = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.22/0.49        | (v2_struct_0 @ sk_B)
% 0.22/0.49        | (v2_struct_0 @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['11', '17'])).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (((v2_struct_0 @ sk_A)
% 0.22/0.49        | ((k2_tsep_1 @ sk_A @ sk_B @ sk_B)
% 0.22/0.49            = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.22/0.49        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 0.22/0.49        | (r1_tsep_1 @ sk_B @ sk_B)
% 0.22/0.49        | (v2_struct_0 @ sk_B))),
% 0.22/0.49      inference('simplify', [status(thm)], ['18'])).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      (((k2_tsep_1 @ sk_A @ sk_B @ sk_B)
% 0.22/0.49         != (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('21', plain,
% 0.22/0.49      (((v2_struct_0 @ sk_A)
% 0.22/0.49        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 0.22/0.49        | (r1_tsep_1 @ sk_B @ sk_B)
% 0.22/0.49        | (v2_struct_0 @ sk_B))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.22/0.49  thf('22', plain,
% 0.22/0.49      ((~ (l1_pre_topc @ sk_B)
% 0.22/0.49        | (v2_struct_0 @ sk_B)
% 0.22/0.49        | (r1_tsep_1 @ sk_B @ sk_B)
% 0.22/0.49        | (v2_struct_0 @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['10', '21'])).
% 0.22/0.49  thf('23', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(dt_m1_pre_topc, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_pre_topc @ A ) =>
% 0.22/0.49       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.22/0.49  thf('24', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (m1_pre_topc @ X0 @ X1) | (l1_pre_topc @ X0) | ~ (l1_pre_topc @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.49  thf('25', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.49  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('27', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.49      inference('demod', [status(thm)], ['25', '26'])).
% 0.22/0.49  thf('28', plain,
% 0.22/0.49      (((v2_struct_0 @ sk_B) | (r1_tsep_1 @ sk_B @ sk_B) | (v2_struct_0 @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['22', '27'])).
% 0.22/0.49  thf('29', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('30', plain, (((v2_struct_0 @ sk_A) | (r1_tsep_1 @ sk_B @ sk_B))),
% 0.22/0.49      inference('clc', [status(thm)], ['28', '29'])).
% 0.22/0.49  thf('31', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('32', plain, ((r1_tsep_1 @ sk_B @ sk_B)),
% 0.22/0.49      inference('clc', [status(thm)], ['30', '31'])).
% 0.22/0.49  thf('33', plain,
% 0.22/0.49      (((v2_struct_0 @ sk_A)
% 0.22/0.49        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 0.22/0.49        | (v2_struct_0 @ sk_B))),
% 0.22/0.49      inference('demod', [status(thm)], ['9', '32'])).
% 0.22/0.49  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('35', plain, (((v2_struct_0 @ sk_B) | ~ (m1_pre_topc @ sk_B @ sk_B))),
% 0.22/0.49      inference('clc', [status(thm)], ['33', '34'])).
% 0.22/0.49  thf('36', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('37', plain, (~ (m1_pre_topc @ sk_B @ sk_B)),
% 0.22/0.49      inference('clc', [status(thm)], ['35', '36'])).
% 0.22/0.49  thf('38', plain, (~ (l1_pre_topc @ sk_B)),
% 0.22/0.49      inference('sup-', [status(thm)], ['0', '37'])).
% 0.22/0.49  thf('39', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.49      inference('demod', [status(thm)], ['25', '26'])).
% 0.22/0.49  thf('40', plain, ($false), inference('demod', [status(thm)], ['38', '39'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
