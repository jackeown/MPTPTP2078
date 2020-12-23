%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jlWC7TAfEY

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 140 expanded)
%              Number of leaves         :   20 (  52 expanded)
%              Depth                    :   13
%              Number of atoms          :  508 (2251 expanded)
%              Number of equality atoms :   12 (  17 expanded)
%              Maximal formula depth    :   18 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_orders_2_type,type,(
    k1_orders_2: $i > $i > $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(a_2_0_orders_2_type,type,(
    a_2_0_orders_2: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(t47_orders_2,conjecture,(
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
                  & ( r2_hidden @ B @ ( k1_orders_2 @ A @ C ) ) ) ) ) ) )).

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
                    & ( r2_hidden @ B @ ( k1_orders_2 @ A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t47_orders_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(irreflexivity_r2_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ~ ( r2_orders_2 @ A @ B @ B ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_orders_2 @ X7 @ X8 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_orders_2 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[irreflexivity_r2_orders_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r2_hidden @ sk_B @ ( k1_orders_2 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fraenkel_a_2_0_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( v3_orders_2 @ B )
        & ( v4_orders_2 @ B )
        & ( v5_orders_2 @ B )
        & ( l1_orders_2 @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
     => ( ( r2_hidden @ A @ ( a_2_0_orders_2 @ B @ C ) )
      <=> ? [D: $i] :
            ( ! [E: $i] :
                ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
               => ( ( r2_hidden @ E @ C )
                 => ( r2_orders_2 @ B @ E @ D ) ) )
            & ( A = D )
            & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( l1_orders_2 @ X2 )
      | ~ ( v5_orders_2 @ X2 )
      | ~ ( v4_orders_2 @ X2 )
      | ~ ( v3_orders_2 @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X2 ) )
      | ( r2_orders_2 @ X2 @ X4 @ ( sk_D @ X3 @ X2 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X5 @ ( a_2_0_orders_2 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ sk_C ) )
      | ~ ( r2_hidden @ X1 @ sk_C )
      | ( r2_orders_2 @ sk_A @ X1 @ ( sk_D @ sk_C @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d12_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_orders_2 @ A @ B )
            = ( a_2_0_orders_2 @ A @ B ) ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( ( k1_orders_2 @ X1 @ X0 )
        = ( a_2_0_orders_2 @ X1 @ X0 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v5_orders_2 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d12_orders_2])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k1_orders_2 @ sk_A @ sk_C )
      = ( a_2_0_orders_2 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_orders_2 @ sk_A @ sk_C )
      = ( a_2_0_orders_2 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k1_orders_2 @ sk_A @ sk_C )
    = ( a_2_0_orders_2 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ sk_C ) )
      | ~ ( r2_hidden @ X1 @ sk_C )
      | ( r2_orders_2 @ sk_A @ X1 @ ( sk_D @ sk_C @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','20','21','22','23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X0 @ ( sk_D @ sk_C @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','25'])).

thf('27',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
    | ( r2_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','26'])).

thf('28',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    r2_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    r2_hidden @ sk_B @ ( k1_orders_2 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ~ ( l1_orders_2 @ X2 )
      | ~ ( v5_orders_2 @ X2 )
      | ~ ( v4_orders_2 @ X2 )
      | ~ ( v3_orders_2 @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( X5
        = ( sk_D @ X3 @ X2 @ X5 ) )
      | ~ ( r2_hidden @ X5 @ ( a_2_0_orders_2 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ sk_C ) )
      | ( X0
        = ( sk_D @ sk_C @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k1_orders_2 @ sk_A @ sk_C )
    = ( a_2_0_orders_2 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('37',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ sk_C ) )
      | ( X0
        = ( sk_D @ sk_C @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36','37','38','39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( sk_D @ sk_C @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,
    ( sk_B
    = ( sk_D @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['32','43'])).

thf('45',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['31','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','45'])).

thf('47',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jlWC7TAfEY
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:47:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 21 iterations in 0.016s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.48  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.21/0.48  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(k1_orders_2_type, type, k1_orders_2: $i > $i > $i).
% 0.21/0.48  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.21/0.48  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.21/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.48  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(a_2_0_orders_2_type, type, a_2_0_orders_2: $i > $i > $i).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.48  thf(t47_orders_2, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.48         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.48           ( ![C:$i]:
% 0.21/0.48             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48               ( ~( ( r2_hidden @ B @ C ) & 
% 0.21/0.48                    ( r2_hidden @ B @ ( k1_orders_2 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.48            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.48          ( ![B:$i]:
% 0.21/0.48            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.48              ( ![C:$i]:
% 0.21/0.48                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48                  ( ~( ( r2_hidden @ B @ C ) & 
% 0.21/0.48                       ( r2_hidden @ B @ ( k1_orders_2 @ A @ C ) ) ) ) ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t47_orders_2])).
% 0.21/0.48  thf('0', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(irreflexivity_r2_orders_2, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.48         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48       ( ~( r2_orders_2 @ A @ B @ B ) ) ))).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.48         (~ (r2_orders_2 @ X7 @ X8 @ X8)
% 0.21/0.48          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.21/0.48          | ~ (l1_orders_2 @ X7)
% 0.21/0.48          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X7)))),
% 0.21/0.48      inference('cnf', [status(esa)], [irreflexivity_r2_orders_2])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.48          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.48          | ~ (r2_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.48  thf('4', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.48          | ~ (r2_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.48  thf('6', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('7', plain, ((r2_hidden @ sk_B @ (k1_orders_2 @ sk_A @ sk_C))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(fraenkel_a_2_0_orders_2, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 0.21/0.48         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 0.21/0.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.21/0.48       ( ( r2_hidden @ A @ ( a_2_0_orders_2 @ B @ C ) ) <=>
% 0.21/0.48         ( ?[D:$i]:
% 0.21/0.48           ( ( ![E:$i]:
% 0.21/0.48               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.48                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ E @ D ) ) ) ) & 
% 0.21/0.48             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.48         (~ (l1_orders_2 @ X2)
% 0.21/0.48          | ~ (v5_orders_2 @ X2)
% 0.21/0.48          | ~ (v4_orders_2 @ X2)
% 0.21/0.48          | ~ (v3_orders_2 @ X2)
% 0.21/0.48          | (v2_struct_0 @ X2)
% 0.21/0.48          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.21/0.48          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X2))
% 0.21/0.48          | (r2_orders_2 @ X2 @ X4 @ (sk_D @ X3 @ X2 @ X5))
% 0.21/0.48          | ~ (r2_hidden @ X4 @ X3)
% 0.21/0.48          | ~ (r2_hidden @ X5 @ (a_2_0_orders_2 @ X2 @ X3)))),
% 0.21/0.48      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ sk_C))
% 0.21/0.48          | ~ (r2_hidden @ X1 @ sk_C)
% 0.21/0.48          | (r2_orders_2 @ sk_A @ X1 @ (sk_D @ sk_C @ sk_A @ X0))
% 0.21/0.48          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.21/0.48          | (v2_struct_0 @ sk_A)
% 0.21/0.48          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.48          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.48          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.48          | ~ (l1_orders_2 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(d12_orders_2, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.48         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48           ( ( k1_orders_2 @ A @ B ) = ( a_2_0_orders_2 @ A @ B ) ) ) ) ))).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.21/0.48          | ((k1_orders_2 @ X1 @ X0) = (a_2_0_orders_2 @ X1 @ X0))
% 0.21/0.48          | ~ (l1_orders_2 @ X1)
% 0.21/0.48          | ~ (v5_orders_2 @ X1)
% 0.21/0.48          | ~ (v4_orders_2 @ X1)
% 0.21/0.48          | ~ (v3_orders_2 @ X1)
% 0.21/0.48          | (v2_struct_0 @ X1))),
% 0.21/0.48      inference('cnf', [status(esa)], [d12_orders_2])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_A)
% 0.21/0.48        | ~ (v3_orders_2 @ sk_A)
% 0.21/0.48        | ~ (v4_orders_2 @ sk_A)
% 0.21/0.48        | ~ (v5_orders_2 @ sk_A)
% 0.21/0.48        | ~ (l1_orders_2 @ sk_A)
% 0.21/0.48        | ((k1_orders_2 @ sk_A @ sk_C) = (a_2_0_orders_2 @ sk_A @ sk_C)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.48  thf('14', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('15', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('16', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('17', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_A)
% 0.21/0.48        | ((k1_orders_2 @ sk_A @ sk_C) = (a_2_0_orders_2 @ sk_A @ sk_C)))),
% 0.21/0.48      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.21/0.48  thf('19', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (((k1_orders_2 @ sk_A @ sk_C) = (a_2_0_orders_2 @ sk_A @ sk_C))),
% 0.21/0.48      inference('clc', [status(thm)], ['18', '19'])).
% 0.21/0.48  thf('21', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('22', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('23', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('24', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X0 @ (k1_orders_2 @ sk_A @ sk_C))
% 0.21/0.48          | ~ (r2_hidden @ X1 @ sk_C)
% 0.21/0.48          | (r2_orders_2 @ sk_A @ X1 @ (sk_D @ sk_C @ sk_A @ X0))
% 0.21/0.48          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.21/0.48          | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['10', '20', '21', '22', '23', '24'])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((v2_struct_0 @ sk_A)
% 0.21/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.48          | (r2_orders_2 @ sk_A @ X0 @ (sk_D @ sk_C @ sk_A @ sk_B))
% 0.21/0.48          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.21/0.48      inference('sup-', [status(thm)], ['7', '25'])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      ((~ (r2_hidden @ sk_B @ sk_C)
% 0.21/0.48        | (r2_orders_2 @ sk_A @ sk_B @ (sk_D @ sk_C @ sk_A @ sk_B))
% 0.21/0.48        | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['6', '26'])).
% 0.21/0.48  thf('28', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      (((r2_orders_2 @ sk_A @ sk_B @ (sk_D @ sk_C @ sk_A @ sk_B))
% 0.21/0.48        | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.48  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('31', plain, ((r2_orders_2 @ sk_A @ sk_B @ (sk_D @ sk_C @ sk_A @ sk_B))),
% 0.21/0.48      inference('clc', [status(thm)], ['29', '30'])).
% 0.21/0.48  thf('32', plain, ((r2_hidden @ sk_B @ (k1_orders_2 @ sk_A @ sk_C))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('33', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('34', plain,
% 0.21/0.48      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.21/0.48         (~ (l1_orders_2 @ X2)
% 0.21/0.48          | ~ (v5_orders_2 @ X2)
% 0.21/0.48          | ~ (v4_orders_2 @ X2)
% 0.21/0.48          | ~ (v3_orders_2 @ X2)
% 0.21/0.48          | (v2_struct_0 @ X2)
% 0.21/0.48          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.21/0.48          | ((X5) = (sk_D @ X3 @ X2 @ X5))
% 0.21/0.48          | ~ (r2_hidden @ X5 @ (a_2_0_orders_2 @ X2 @ X3)))),
% 0.21/0.48      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 0.21/0.48  thf('35', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ sk_C))
% 0.21/0.48          | ((X0) = (sk_D @ sk_C @ sk_A @ X0))
% 0.21/0.48          | (v2_struct_0 @ sk_A)
% 0.21/0.48          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.48          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.48          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.48          | ~ (l1_orders_2 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.48  thf('36', plain,
% 0.21/0.48      (((k1_orders_2 @ sk_A @ sk_C) = (a_2_0_orders_2 @ sk_A @ sk_C))),
% 0.21/0.48      inference('clc', [status(thm)], ['18', '19'])).
% 0.21/0.48  thf('37', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('38', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('39', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('40', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('41', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X0 @ (k1_orders_2 @ sk_A @ sk_C))
% 0.21/0.48          | ((X0) = (sk_D @ sk_C @ sk_A @ X0))
% 0.21/0.48          | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['35', '36', '37', '38', '39', '40'])).
% 0.21/0.48  thf('42', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('43', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((X0) = (sk_D @ sk_C @ sk_A @ X0))
% 0.21/0.48          | ~ (r2_hidden @ X0 @ (k1_orders_2 @ sk_A @ sk_C)))),
% 0.21/0.48      inference('clc', [status(thm)], ['41', '42'])).
% 0.21/0.48  thf('44', plain, (((sk_B) = (sk_D @ sk_C @ sk_A @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['32', '43'])).
% 0.21/0.48  thf('45', plain, ((r2_orders_2 @ sk_A @ sk_B @ sk_B)),
% 0.21/0.48      inference('demod', [status(thm)], ['31', '44'])).
% 0.21/0.48  thf('46', plain, (![X0 : $i]: ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['5', '45'])).
% 0.21/0.48  thf('47', plain, ($false), inference('sup-', [status(thm)], ['0', '46'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
