%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.n1TgpTGnfA

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 138 expanded)
%              Number of leaves         :   21 (  52 expanded)
%              Depth                    :   13
%              Number of atoms          :  510 (2199 expanded)
%              Number of equality atoms :   14 (  19 expanded)
%              Maximal formula depth    :   18 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(k2_orders_2_type,type,(
    k2_orders_2: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(a_2_1_orders_2_type,type,(
    a_2_1_orders_2: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(t49_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ~ ( ( r2_hidden @ B @ C )
                  & ( r2_hidden @ B @ ( k2_orders_2 @ A @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ~ ( ( r2_hidden @ B @ C )
                    & ( r2_hidden @ B @ ( k2_orders_2 @ A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_orders_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fraenkel_a_2_1_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( v3_orders_2 @ B )
        & ( v4_orders_2 @ B )
        & ( v5_orders_2 @ B )
        & ( l1_orders_2 @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
     => ( ( r2_hidden @ A @ ( a_2_1_orders_2 @ B @ C ) )
      <=> ? [D: $i] :
            ( ! [E: $i] :
                ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
               => ( ( r2_hidden @ E @ C )
                 => ( r2_orders_2 @ B @ D @ E ) ) )
            & ( A = D )
            & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_orders_2 @ X5 )
      | ~ ( v5_orders_2 @ X5 )
      | ~ ( v4_orders_2 @ X5 )
      | ~ ( v3_orders_2 @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X5 ) )
      | ( r2_orders_2 @ X5 @ ( sk_D @ X6 @ X5 @ X8 ) @ X7 )
      | ~ ( r2_hidden @ X7 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( a_2_1_orders_2 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ sk_C ) )
      | ~ ( r2_hidden @ X1 @ sk_C )
      | ( r2_orders_2 @ sk_A @ ( sk_D @ sk_C @ sk_A @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d13_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_orders_2 @ A @ B )
            = ( a_2_1_orders_2 @ A @ B ) ) ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( ( k2_orders_2 @ X4 @ X3 )
        = ( a_2_1_orders_2 @ X4 @ X3 ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v5_orders_2 @ X4 )
      | ~ ( v4_orders_2 @ X4 )
      | ~ ( v3_orders_2 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d13_orders_2])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k2_orders_2 @ sk_A @ sk_C )
      = ( a_2_1_orders_2 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_orders_2 @ sk_A @ sk_C )
      = ( a_2_1_orders_2 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['8','9','10','11','12'])).

thf('14',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k2_orders_2 @ sk_A @ sk_C )
    = ( a_2_1_orders_2 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ sk_C ) )
      | ~ ( r2_hidden @ X1 @ sk_C )
      | ( r2_orders_2 @ sk_A @ ( sk_D @ sk_C @ sk_A @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','15','16','17','18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ ( sk_D @ sk_C @ sk_A @ sk_B ) @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','20'])).

thf('22',plain,(
    r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( l1_orders_2 @ X5 )
      | ~ ( v5_orders_2 @ X5 )
      | ~ ( v4_orders_2 @ X5 )
      | ~ ( v3_orders_2 @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( X8
        = ( sk_D @ X6 @ X5 @ X8 ) )
      | ~ ( r2_hidden @ X8 @ ( a_2_1_orders_2 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ sk_C ) )
      | ( X0
        = ( sk_D @ sk_C @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k2_orders_2 @ sk_A @ sk_C )
    = ( a_2_1_orders_2 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('27',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ sk_C ) )
      | ( X0
        = ( sk_D @ sk_C @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26','27','28','29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( sk_D @ sk_C @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,
    ( sk_B
    = ( sk_D @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['22','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['21','34'])).

thf('36',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
    | ( r2_orders_2 @ sk_A @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','35'])).

thf('37',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_orders_2 @ A @ B @ C )
              <=> ( ( r1_orders_2 @ A @ B @ C )
                  & ( B != C ) ) ) ) ) ) )).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_orders_2 @ X1 @ X0 @ X2 )
      | ( X0 != X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('41',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ~ ( r2_orders_2 @ X1 @ X2 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_B )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['38','44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['0','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.n1TgpTGnfA
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:42:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 33 iterations in 0.024s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.20/0.46  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.46  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.20/0.46  thf(k2_orders_2_type, type, k2_orders_2: $i > $i > $i).
% 0.20/0.46  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(a_2_1_orders_2_type, type, a_2_1_orders_2: $i > $i > $i).
% 0.20/0.46  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.46  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.46  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.46  thf(t49_orders_2, conjecture,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.46         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.46       ( ![B:$i]:
% 0.20/0.46         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.46           ( ![C:$i]:
% 0.20/0.46             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.46               ( ~( ( r2_hidden @ B @ C ) & 
% 0.20/0.46                    ( r2_hidden @ B @ ( k2_orders_2 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i]:
% 0.20/0.46        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.46            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.46          ( ![B:$i]:
% 0.20/0.46            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.46              ( ![C:$i]:
% 0.20/0.46                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.46                  ( ~( ( r2_hidden @ B @ C ) & 
% 0.20/0.46                       ( r2_hidden @ B @ ( k2_orders_2 @ A @ C ) ) ) ) ) ) ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t49_orders_2])).
% 0.20/0.46  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('2', plain, ((r2_hidden @ sk_B @ (k2_orders_2 @ sk_A @ sk_C))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(fraenkel_a_2_1_orders_2, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 0.20/0.46         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 0.20/0.46         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.20/0.46       ( ( r2_hidden @ A @ ( a_2_1_orders_2 @ B @ C ) ) <=>
% 0.20/0.46         ( ?[D:$i]:
% 0.20/0.46           ( ( ![E:$i]:
% 0.20/0.46               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.46                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ D @ E ) ) ) ) & 
% 0.20/0.47             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.47         (~ (l1_orders_2 @ X5)
% 0.20/0.47          | ~ (v5_orders_2 @ X5)
% 0.20/0.47          | ~ (v4_orders_2 @ X5)
% 0.20/0.47          | ~ (v3_orders_2 @ X5)
% 0.20/0.47          | (v2_struct_0 @ X5)
% 0.20/0.47          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.20/0.47          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X5))
% 0.20/0.47          | (r2_orders_2 @ X5 @ (sk_D @ X6 @ X5 @ X8) @ X7)
% 0.20/0.47          | ~ (r2_hidden @ X7 @ X6)
% 0.20/0.47          | ~ (r2_hidden @ X8 @ (a_2_1_orders_2 @ X5 @ X6)))),
% 0.20/0.47      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ sk_C))
% 0.20/0.47          | ~ (r2_hidden @ X1 @ sk_C)
% 0.20/0.47          | (r2_orders_2 @ sk_A @ (sk_D @ sk_C @ sk_A @ X0) @ X1)
% 0.20/0.47          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.20/0.47          | (v2_struct_0 @ sk_A)
% 0.20/0.47          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.47          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.47          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.47          | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(d13_orders_2, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.47         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47           ( ( k2_orders_2 @ A @ B ) = ( a_2_1_orders_2 @ A @ B ) ) ) ) ))).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.47          | ((k2_orders_2 @ X4 @ X3) = (a_2_1_orders_2 @ X4 @ X3))
% 0.20/0.47          | ~ (l1_orders_2 @ X4)
% 0.20/0.47          | ~ (v5_orders_2 @ X4)
% 0.20/0.47          | ~ (v4_orders_2 @ X4)
% 0.20/0.47          | ~ (v3_orders_2 @ X4)
% 0.20/0.47          | (v2_struct_0 @ X4))),
% 0.20/0.47      inference('cnf', [status(esa)], [d13_orders_2])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | ~ (v3_orders_2 @ sk_A)
% 0.20/0.47        | ~ (v4_orders_2 @ sk_A)
% 0.20/0.47        | ~ (v5_orders_2 @ sk_A)
% 0.20/0.47        | ~ (l1_orders_2 @ sk_A)
% 0.20/0.47        | ((k2_orders_2 @ sk_A @ sk_C) = (a_2_1_orders_2 @ sk_A @ sk_C)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.47  thf('9', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('10', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('11', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('12', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | ((k2_orders_2 @ sk_A @ sk_C) = (a_2_1_orders_2 @ sk_A @ sk_C)))),
% 0.20/0.47      inference('demod', [status(thm)], ['8', '9', '10', '11', '12'])).
% 0.20/0.47  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (((k2_orders_2 @ sk_A @ sk_C) = (a_2_1_orders_2 @ sk_A @ sk_C))),
% 0.20/0.47      inference('clc', [status(thm)], ['13', '14'])).
% 0.20/0.47  thf('16', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('17', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('18', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('19', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X0 @ (k2_orders_2 @ sk_A @ sk_C))
% 0.20/0.47          | ~ (r2_hidden @ X1 @ sk_C)
% 0.20/0.47          | (r2_orders_2 @ sk_A @ (sk_D @ sk_C @ sk_A @ X0) @ X1)
% 0.20/0.47          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.20/0.47          | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['5', '15', '16', '17', '18', '19'])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_struct_0 @ sk_A)
% 0.20/0.47          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.47          | (r2_orders_2 @ sk_A @ (sk_D @ sk_C @ sk_A @ sk_B) @ X0)
% 0.20/0.47          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['2', '20'])).
% 0.20/0.47  thf('22', plain, ((r2_hidden @ sk_B @ (k2_orders_2 @ sk_A @ sk_C))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('24', plain,
% 0.20/0.47      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.20/0.47         (~ (l1_orders_2 @ X5)
% 0.20/0.47          | ~ (v5_orders_2 @ X5)
% 0.20/0.47          | ~ (v4_orders_2 @ X5)
% 0.20/0.47          | ~ (v3_orders_2 @ X5)
% 0.20/0.47          | (v2_struct_0 @ X5)
% 0.20/0.47          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.20/0.47          | ((X8) = (sk_D @ X6 @ X5 @ X8))
% 0.20/0.47          | ~ (r2_hidden @ X8 @ (a_2_1_orders_2 @ X5 @ X6)))),
% 0.20/0.47      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ sk_C))
% 0.20/0.47          | ((X0) = (sk_D @ sk_C @ sk_A @ X0))
% 0.20/0.47          | (v2_struct_0 @ sk_A)
% 0.20/0.47          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.47          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.47          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.47          | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      (((k2_orders_2 @ sk_A @ sk_C) = (a_2_1_orders_2 @ sk_A @ sk_C))),
% 0.20/0.47      inference('clc', [status(thm)], ['13', '14'])).
% 0.20/0.47  thf('27', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('28', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('29', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('30', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('31', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X0 @ (k2_orders_2 @ sk_A @ sk_C))
% 0.20/0.47          | ((X0) = (sk_D @ sk_C @ sk_A @ X0))
% 0.20/0.47          | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['25', '26', '27', '28', '29', '30'])).
% 0.20/0.47  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('33', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((X0) = (sk_D @ sk_C @ sk_A @ X0))
% 0.20/0.47          | ~ (r2_hidden @ X0 @ (k2_orders_2 @ sk_A @ sk_C)))),
% 0.20/0.47      inference('clc', [status(thm)], ['31', '32'])).
% 0.20/0.47  thf('34', plain, (((sk_B) = (sk_D @ sk_C @ sk_A @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['22', '33'])).
% 0.20/0.47  thf('35', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_struct_0 @ sk_A)
% 0.20/0.47          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.47          | (r2_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.47          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.20/0.47      inference('demod', [status(thm)], ['21', '34'])).
% 0.20/0.47  thf('36', plain,
% 0.20/0.47      ((~ (r2_hidden @ sk_B @ sk_C)
% 0.20/0.47        | (r2_orders_2 @ sk_A @ sk_B @ sk_B)
% 0.20/0.47        | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '35'])).
% 0.20/0.47  thf('37', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('38', plain,
% 0.20/0.47      (((r2_orders_2 @ sk_A @ sk_B @ sk_B) | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.47  thf('39', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(d10_orders_2, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_orders_2 @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.47           ( ![C:$i]:
% 0.20/0.47             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.47               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.20/0.47                 ( ( r1_orders_2 @ A @ B @ C ) & ( ( B ) != ( C ) ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf('40', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.20/0.47          | ~ (r2_orders_2 @ X1 @ X0 @ X2)
% 0.20/0.47          | ((X0) != (X2))
% 0.20/0.47          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.47          | ~ (l1_orders_2 @ X1))),
% 0.20/0.47      inference('cnf', [status(esa)], [d10_orders_2])).
% 0.20/0.47  thf('41', plain,
% 0.20/0.47      (![X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (l1_orders_2 @ X1)
% 0.20/0.47          | ~ (r2_orders_2 @ X1 @ X2 @ X2)
% 0.20/0.47          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['40'])).
% 0.20/0.47  thf('42', plain,
% 0.20/0.47      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_B) | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['39', '41'])).
% 0.20/0.47  thf('43', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('44', plain, (~ (r2_orders_2 @ sk_A @ sk_B @ sk_B)),
% 0.20/0.47      inference('demod', [status(thm)], ['42', '43'])).
% 0.20/0.47  thf('45', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('clc', [status(thm)], ['38', '44'])).
% 0.20/0.47  thf('46', plain, ($false), inference('demod', [status(thm)], ['0', '45'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
