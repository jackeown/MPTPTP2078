%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.og3zDrlDty

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 107 expanded)
%              Number of leaves         :   17 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :  526 (1373 expanded)
%              Number of equality atoms :   15 (  53 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tsep_1_type,type,(
    k2_tsep_1: $i > $i > $i > $i )).

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

thf('0',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
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

thf('2',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( m1_pre_topc @ X3 @ X4 )
      | ~ ( m1_pre_topc @ X3 @ X5 )
      | ~ ( r1_tsep_1 @ X5 @ X3 )
      | ~ ( m1_pre_topc @ X5 @ X4 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t22_tmap_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tsep_1 @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tsep_1 @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( r1_tsep_1 @ sk_B @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t4_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) )
              <=> ( m1_pre_topc @ B @ C ) ) ) ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X11 ) )
      | ( m1_pre_topc @ X9 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( r1_tsep_1 @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['8','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_B ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_B ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
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

thf('26',plain,(
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

thf('27',plain,(
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
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( k2_tsep_1 @ sk_A @ sk_B @ X0 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( ( k2_tsep_1 @ sk_A @ sk_B @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_B )
    | ( ( k2_tsep_1 @ sk_A @ sk_B @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tsep_1 @ sk_A @ sk_B @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( r1_tsep_1 @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ( k2_tsep_1 @ sk_A @ sk_B @ sk_B )
 != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tsep_1 @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_B ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r1_tsep_1 @ sk_B @ sk_B ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['23','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.og3zDrlDty
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:46:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 29 iterations in 0.022s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.47  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.47  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.21/0.47  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.21/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(k2_tsep_1_type, type, k2_tsep_1: $i > $i > $i > $i).
% 0.21/0.47  thf(t26_tmap_1, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.47           ( ( k2_tsep_1 @ A @ B @ B ) =
% 0.21/0.47             ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.47            ( l1_pre_topc @ A ) ) =>
% 0.21/0.47          ( ![B:$i]:
% 0.21/0.47            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.47              ( ( k2_tsep_1 @ A @ B @ B ) =
% 0.21/0.47                ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t26_tmap_1])).
% 0.21/0.47  thf('0', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t22_tmap_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.47           ( ![C:$i]:
% 0.21/0.47             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.47               ( ( m1_pre_topc @ B @ C ) =>
% 0.21/0.47                 ( ( ~( r1_tsep_1 @ B @ C ) ) & ( ~( r1_tsep_1 @ C @ B ) ) ) ) ) ) ) ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.47         ((v2_struct_0 @ X3)
% 0.21/0.47          | ~ (m1_pre_topc @ X3 @ X4)
% 0.21/0.47          | ~ (m1_pre_topc @ X3 @ X5)
% 0.21/0.47          | ~ (r1_tsep_1 @ X5 @ X3)
% 0.21/0.47          | ~ (m1_pre_topc @ X5 @ X4)
% 0.21/0.47          | (v2_struct_0 @ X5)
% 0.21/0.47          | ~ (l1_pre_topc @ X4)
% 0.21/0.47          | ~ (v2_pre_topc @ X4)
% 0.21/0.47          | (v2_struct_0 @ X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [t22_tmap_1])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((v2_struct_0 @ sk_A)
% 0.21/0.47          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.47          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.47          | (v2_struct_0 @ X0)
% 0.21/0.47          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.47          | ~ (r1_tsep_1 @ X0 @ sk_B)
% 0.21/0.47          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.21/0.47          | (v2_struct_0 @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((v2_struct_0 @ sk_A)
% 0.21/0.47          | (v2_struct_0 @ X0)
% 0.21/0.47          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.47          | ~ (r1_tsep_1 @ X0 @ sk_B)
% 0.21/0.47          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.21/0.47          | (v2_struct_0 @ sk_B))),
% 0.21/0.47      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (((v2_struct_0 @ sk_B)
% 0.21/0.47        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 0.21/0.47        | ~ (r1_tsep_1 @ sk_B @ sk_B)
% 0.21/0.47        | (v2_struct_0 @ sk_B)
% 0.21/0.47        | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '6'])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (((v2_struct_0 @ sk_A)
% 0.21/0.47        | ~ (r1_tsep_1 @ sk_B @ sk_B)
% 0.21/0.47        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 0.21/0.47        | (v2_struct_0 @ sk_B))),
% 0.21/0.47      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.47  thf('9', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(d10_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.47  thf('11', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.47      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.47  thf(t4_tsep_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.47           ( ![C:$i]:
% 0.21/0.47             ( ( m1_pre_topc @ C @ A ) =>
% 0.21/0.47               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.21/0.47                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.47         (~ (m1_pre_topc @ X9 @ X10)
% 0.21/0.47          | ~ (r1_tarski @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X11))
% 0.21/0.47          | (m1_pre_topc @ X9 @ X11)
% 0.21/0.47          | ~ (m1_pre_topc @ X11 @ X10)
% 0.21/0.47          | ~ (l1_pre_topc @ X10)
% 0.21/0.47          | ~ (v2_pre_topc @ X10))),
% 0.21/0.47      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (v2_pre_topc @ X1)
% 0.21/0.47          | ~ (l1_pre_topc @ X1)
% 0.21/0.47          | ~ (m1_pre_topc @ X0 @ X1)
% 0.21/0.47          | (m1_pre_topc @ X0 @ X0)
% 0.21/0.47          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((m1_pre_topc @ X0 @ X0)
% 0.21/0.47          | ~ (m1_pre_topc @ X0 @ X1)
% 0.21/0.47          | ~ (l1_pre_topc @ X1)
% 0.21/0.47          | ~ (v2_pre_topc @ X1))),
% 0.21/0.47      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      ((~ (v2_pre_topc @ sk_A)
% 0.21/0.47        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.47        | (m1_pre_topc @ sk_B @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['9', '14'])).
% 0.21/0.47  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('18', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 0.21/0.47      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (((v2_struct_0 @ sk_A)
% 0.21/0.47        | ~ (r1_tsep_1 @ sk_B @ sk_B)
% 0.21/0.47        | (v2_struct_0 @ sk_B))),
% 0.21/0.47      inference('demod', [status(thm)], ['8', '18'])).
% 0.21/0.47  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('21', plain, (((v2_struct_0 @ sk_B) | ~ (r1_tsep_1 @ sk_B @ sk_B))),
% 0.21/0.47      inference('clc', [status(thm)], ['19', '20'])).
% 0.21/0.47  thf('22', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('23', plain, (~ (r1_tsep_1 @ sk_B @ sk_B)),
% 0.21/0.47      inference('clc', [status(thm)], ['21', '22'])).
% 0.21/0.47  thf('24', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('25', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t31_tsep_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.47           ( ![C:$i]:
% 0.21/0.47             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.47               ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 0.21/0.47                 ( ( ( m1_pre_topc @ B @ C ) =>
% 0.21/0.47                     ( ( k2_tsep_1 @ A @ B @ C ) =
% 0.21/0.47                       ( g1_pre_topc @
% 0.21/0.47                         ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) & 
% 0.21/0.47                   ( ( ( k2_tsep_1 @ A @ B @ C ) =
% 0.21/0.47                       ( g1_pre_topc @
% 0.21/0.47                         ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.21/0.47                     ( m1_pre_topc @ B @ C ) ) & 
% 0.21/0.47                   ( ( m1_pre_topc @ C @ B ) =>
% 0.21/0.47                     ( ( k2_tsep_1 @ A @ B @ C ) =
% 0.21/0.47                       ( g1_pre_topc @
% 0.21/0.47                         ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) ) & 
% 0.21/0.47                   ( ( ( k2_tsep_1 @ A @ B @ C ) =
% 0.21/0.47                       ( g1_pre_topc @
% 0.21/0.47                         ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) =>
% 0.21/0.47                     ( m1_pre_topc @ C @ B ) ) ) ) ) ) ) ) ))).
% 0.21/0.47  thf('26', plain,
% 0.21/0.47      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.47         ((v2_struct_0 @ X6)
% 0.21/0.47          | ~ (m1_pre_topc @ X6 @ X7)
% 0.21/0.47          | (r1_tsep_1 @ X6 @ X8)
% 0.21/0.47          | ~ (m1_pre_topc @ X8 @ X6)
% 0.21/0.47          | ((k2_tsep_1 @ X7 @ X6 @ X8)
% 0.21/0.47              = (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)))
% 0.21/0.47          | ~ (m1_pre_topc @ X8 @ X7)
% 0.21/0.47          | (v2_struct_0 @ X8)
% 0.21/0.47          | ~ (l1_pre_topc @ X7)
% 0.21/0.47          | ~ (v2_pre_topc @ X7)
% 0.21/0.47          | (v2_struct_0 @ X7))),
% 0.21/0.47      inference('cnf', [status(esa)], [t31_tsep_1])).
% 0.21/0.47  thf('27', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((v2_struct_0 @ sk_A)
% 0.21/0.47          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.47          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.47          | (v2_struct_0 @ X0)
% 0.21/0.47          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.47          | ((k2_tsep_1 @ sk_A @ sk_B @ X0)
% 0.21/0.47              = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.21/0.47          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.47          | (r1_tsep_1 @ sk_B @ X0)
% 0.21/0.47          | (v2_struct_0 @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.47  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('30', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((v2_struct_0 @ sk_A)
% 0.21/0.47          | (v2_struct_0 @ X0)
% 0.21/0.47          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.47          | ((k2_tsep_1 @ sk_A @ sk_B @ X0)
% 0.21/0.47              = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.21/0.47          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.47          | (r1_tsep_1 @ sk_B @ X0)
% 0.21/0.47          | (v2_struct_0 @ sk_B))),
% 0.21/0.47      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.21/0.47  thf('31', plain,
% 0.21/0.47      (((v2_struct_0 @ sk_B)
% 0.21/0.47        | (r1_tsep_1 @ sk_B @ sk_B)
% 0.21/0.47        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 0.21/0.47        | ((k2_tsep_1 @ sk_A @ sk_B @ sk_B)
% 0.21/0.47            = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.21/0.47        | (v2_struct_0 @ sk_B)
% 0.21/0.47        | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['24', '30'])).
% 0.21/0.47  thf('32', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 0.21/0.47      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.21/0.47  thf('33', plain,
% 0.21/0.47      (((v2_struct_0 @ sk_B)
% 0.21/0.47        | (r1_tsep_1 @ sk_B @ sk_B)
% 0.21/0.47        | ((k2_tsep_1 @ sk_A @ sk_B @ sk_B)
% 0.21/0.47            = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.21/0.47        | (v2_struct_0 @ sk_B)
% 0.21/0.47        | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.47  thf('34', plain,
% 0.21/0.47      (((v2_struct_0 @ sk_A)
% 0.21/0.47        | ((k2_tsep_1 @ sk_A @ sk_B @ sk_B)
% 0.21/0.47            = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.21/0.47        | (r1_tsep_1 @ sk_B @ sk_B)
% 0.21/0.47        | (v2_struct_0 @ sk_B))),
% 0.21/0.47      inference('simplify', [status(thm)], ['33'])).
% 0.21/0.47  thf('35', plain,
% 0.21/0.47      (((k2_tsep_1 @ sk_A @ sk_B @ sk_B)
% 0.21/0.47         != (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('36', plain,
% 0.21/0.47      (((v2_struct_0 @ sk_A) | (r1_tsep_1 @ sk_B @ sk_B) | (v2_struct_0 @ sk_B))),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['34', '35'])).
% 0.21/0.47  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('38', plain, (((v2_struct_0 @ sk_B) | (r1_tsep_1 @ sk_B @ sk_B))),
% 0.21/0.47      inference('clc', [status(thm)], ['36', '37'])).
% 0.21/0.47  thf('39', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('40', plain, ((r1_tsep_1 @ sk_B @ sk_B)),
% 0.21/0.47      inference('clc', [status(thm)], ['38', '39'])).
% 0.21/0.47  thf('41', plain, ($false), inference('demod', [status(thm)], ['23', '40'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
