%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8llLeaMcH7

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 154 expanded)
%              Number of leaves         :   18 (  51 expanded)
%              Depth                    :   16
%              Number of atoms          :  402 (1859 expanded)
%              Number of equality atoms :   21 (  79 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( m1_pre_topc @ X2 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t16_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_tex_2 @ B @ A )
            & ( m1_pre_topc @ B @ A ) )
         => ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) )
            = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v1_tex_2 @ B @ A )
              & ( m1_pre_topc @ B @ A ) )
           => ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) )
              = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t16_tex_2])).

thf('1',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X7 = X6 )
      | ( v1_subset_1 @ X7 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('8',plain,
    ( ( v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t13_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                <=> ( v1_tex_2 @ B @ A ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( X10
       != ( u1_struct_0 @ X8 ) )
      | ~ ( v1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( v1_tex_2 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t13_tex_2])).

thf('11',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v1_tex_2 @ X8 @ X9 )
      | ~ ( v1_subset_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_pre_topc @ X8 @ X9 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ~ ( v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ~ ( v1_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ~ ( v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','17'])).

thf(t5_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( ( u1_struct_0 @ B )
                  = ( u1_struct_0 @ C ) )
               => ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) )
                  = ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( ( u1_struct_0 @ X3 )
       != ( u1_struct_0 @ X5 ) )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X3 ) @ ( u1_pre_topc @ X3 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X5 ) @ ( u1_pre_topc @ X5 ) ) )
      | ~ ( m1_pre_topc @ X5 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[t5_tsep_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ X0 )
       != ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','17'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ X0 )
       != ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(eq_res,[status(thm)],['22'])).

thf('24',plain,(
    ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
 != ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','17'])).

thf('26',plain,(
    ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
 != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['23','26'])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_pre_topc @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['1','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ~ ( m1_pre_topc @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['31','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8llLeaMcH7
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:12:11 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running portfolio for 600 s
% 0.20/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 50 iterations in 0.024s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.47  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.21/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.47  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.21/0.47  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(t2_tsep_1, axiom,
% 0.21/0.47    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      (![X2 : $i]: ((m1_pre_topc @ X2 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.21/0.47      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.21/0.47  thf(t16_tex_2, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( ( ~( v1_tex_2 @ B @ A ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.47           ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) =
% 0.21/0.47             ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.47          ( ![B:$i]:
% 0.21/0.47            ( ( ( ~( v1_tex_2 @ B @ A ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.47              ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) =
% 0.21/0.47                ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t16_tex_2])).
% 0.21/0.47  thf('1', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t1_tsep_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( l1_pre_topc @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.47           ( m1_subset_1 @
% 0.21/0.47             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (m1_pre_topc @ X0 @ X1)
% 0.21/0.47          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.21/0.47             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.21/0.47          | ~ (l1_pre_topc @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.47        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.47           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.47  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.47        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.47      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.47  thf(d7_subset_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.47       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X6 : $i, X7 : $i]:
% 0.21/0.47         (((X7) = (X6))
% 0.21/0.47          | (v1_subset_1 @ X7 @ X6)
% 0.21/0.47          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (((v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.47        | ((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.47        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.47      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.47  thf(t13_tex_2, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( l1_pre_topc @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.47           ( ![C:$i]:
% 0.21/0.47             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.21/0.47                 ( ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) <=>
% 0.21/0.47                   ( v1_tex_2 @ B @ A ) ) ) ) ) ) ) ))).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.47         (~ (m1_pre_topc @ X8 @ X9)
% 0.21/0.47          | ((X10) != (u1_struct_0 @ X8))
% 0.21/0.47          | ~ (v1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.21/0.47          | (v1_tex_2 @ X8 @ X9)
% 0.21/0.47          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.21/0.47          | ~ (l1_pre_topc @ X9))),
% 0.21/0.47      inference('cnf', [status(esa)], [t13_tex_2])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X8 : $i, X9 : $i]:
% 0.21/0.47         (~ (l1_pre_topc @ X9)
% 0.21/0.47          | ~ (m1_subset_1 @ (u1_struct_0 @ X8) @ 
% 0.21/0.47               (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.21/0.47          | (v1_tex_2 @ X8 @ X9)
% 0.21/0.47          | ~ (v1_subset_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X9))
% 0.21/0.47          | ~ (m1_pre_topc @ X8 @ X9))),
% 0.21/0.47      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.21/0.47        | ~ (v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.47        | (v1_tex_2 @ sk_B @ sk_A)
% 0.21/0.47        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['9', '11'])).
% 0.21/0.47  thf('13', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      ((~ (v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.47        | (v1_tex_2 @ sk_B @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.21/0.47  thf('16', plain, (~ (v1_tex_2 @ sk_B @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (~ (v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.47      inference('clc', [status(thm)], ['15', '16'])).
% 0.21/0.47  thf('18', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['8', '17'])).
% 0.21/0.47  thf(t5_tsep_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( l1_pre_topc @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.47           ( ![C:$i]:
% 0.21/0.47             ( ( m1_pre_topc @ C @ A ) =>
% 0.21/0.47               ( ( ( u1_struct_0 @ B ) = ( u1_struct_0 @ C ) ) =>
% 0.21/0.47                 ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) =
% 0.21/0.47                   ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) ) ) ) ) ) ))).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.47         (~ (m1_pre_topc @ X3 @ X4)
% 0.21/0.47          | ((u1_struct_0 @ X3) != (u1_struct_0 @ X5))
% 0.21/0.47          | ((g1_pre_topc @ (u1_struct_0 @ X3) @ (u1_pre_topc @ X3))
% 0.21/0.47              = (g1_pre_topc @ (u1_struct_0 @ X5) @ (u1_pre_topc @ X5)))
% 0.21/0.47          | ~ (m1_pre_topc @ X5 @ X4)
% 0.21/0.47          | ~ (l1_pre_topc @ X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [t5_tsep_1])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (((u1_struct_0 @ X0) != (u1_struct_0 @ sk_B))
% 0.21/0.47          | ~ (l1_pre_topc @ X1)
% 0.21/0.47          | ~ (m1_pre_topc @ sk_A @ X1)
% 0.21/0.47          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.21/0.47              = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.47          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.47  thf('21', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['8', '17'])).
% 0.21/0.47  thf('22', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (((u1_struct_0 @ X0) != (u1_struct_0 @ sk_B))
% 0.21/0.47          | ~ (l1_pre_topc @ X1)
% 0.21/0.47          | ~ (m1_pre_topc @ sk_A @ X1)
% 0.21/0.47          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.21/0.47              = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 0.21/0.47          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.21/0.47      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.47  thf('23', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (m1_pre_topc @ sk_B @ X0)
% 0.21/0.47          | ((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.21/0.47              = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 0.21/0.47          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.21/0.47          | ~ (l1_pre_topc @ X0))),
% 0.21/0.47      inference('eq_res', [status(thm)], ['22'])).
% 0.21/0.47  thf('24', plain,
% 0.21/0.47      (((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.21/0.47         != (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('25', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['8', '17'])).
% 0.21/0.47  thf('26', plain,
% 0.21/0.47      (((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.21/0.47         != (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.21/0.47      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.47  thf('27', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (m1_pre_topc @ sk_B @ X0)
% 0.21/0.47          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.21/0.47          | ~ (l1_pre_topc @ X0))),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['23', '26'])).
% 0.21/0.47  thf('28', plain, ((~ (l1_pre_topc @ sk_A) | ~ (m1_pre_topc @ sk_A @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '27'])).
% 0.21/0.47  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('30', plain, (~ (m1_pre_topc @ sk_A @ sk_A)),
% 0.21/0.47      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.47  thf('31', plain, (~ (l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '30'])).
% 0.21/0.47  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('33', plain, ($false), inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
