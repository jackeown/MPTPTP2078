%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nY8X7udyPN

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 144 expanded)
%              Number of leaves         :   20 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :  540 (2337 expanded)
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

thf(t28_orders_2,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ~ ( ( r2_orders_2 @ A @ B @ C )
                  & ( r2_orders_2 @ A @ C @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r2_orders_2 @ X8 @ X9 @ X7 )
      | ~ ( r2_orders_2 @ X8 @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v5_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_orders_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_B )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,(
    ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    r2_hidden @ sk_B @ ( k1_orders_2 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
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

thf('12',plain,(
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

thf('13',plain,(
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
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
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

thf('15',plain,(
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

thf('16',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k1_orders_2 @ sk_A @ sk_C )
      = ( a_2_0_orders_2 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_orders_2 @ sk_A @ sk_C )
      = ( a_2_0_orders_2 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k1_orders_2 @ sk_A @ sk_C )
    = ( a_2_0_orders_2 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ sk_C ) )
      | ~ ( r2_hidden @ X1 @ sk_C )
      | ( r2_orders_2 @ sk_A @ X1 @ ( sk_D @ sk_C @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','23','24','25','26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X0 @ ( sk_D @ sk_C @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','28'])).

thf('30',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
    | ( r2_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','29'])).

thf('31',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    r2_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    r2_hidden @ sk_B @ ( k1_orders_2 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
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

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ sk_C ) )
      | ( X0
        = ( sk_D @ sk_C @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k1_orders_2 @ sk_A @ sk_C )
    = ( a_2_0_orders_2 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('40',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ sk_C ) )
      | ( X0
        = ( sk_D @ sk_C @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39','40','41','42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( sk_D @ sk_C @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,
    ( sk_B
    = ( sk_D @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['35','46'])).

thf('48',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['34','47'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['8','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nY8X7udyPN
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:28:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 21 iterations in 0.017s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.46  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.46  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(k1_orders_2_type, type, k1_orders_2: $i > $i > $i).
% 0.20/0.46  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.20/0.46  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.46  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(a_2_0_orders_2_type, type, a_2_0_orders_2: $i > $i > $i).
% 0.20/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.46  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.46  thf(t47_orders_2, conjecture,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.46         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.46       ( ![B:$i]:
% 0.20/0.46         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.46           ( ![C:$i]:
% 0.20/0.46             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.46               ( ~( ( r2_hidden @ B @ C ) & 
% 0.20/0.46                    ( r2_hidden @ B @ ( k1_orders_2 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i]:
% 0.20/0.46        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.46            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.46          ( ![B:$i]:
% 0.20/0.46            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.46              ( ![C:$i]:
% 0.20/0.46                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.46                  ( ~( ( r2_hidden @ B @ C ) & 
% 0.20/0.46                       ( r2_hidden @ B @ ( k1_orders_2 @ A @ C ) ) ) ) ) ) ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t47_orders_2])).
% 0.20/0.46  thf('0', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(t28_orders_2, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.46       ( ![B:$i]:
% 0.20/0.46         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.46           ( ![C:$i]:
% 0.20/0.46             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.46               ( ~( ( r2_orders_2 @ A @ B @ C ) & ( r2_orders_2 @ A @ C @ B ) ) ) ) ) ) ) ))).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.20/0.46          | ~ (r2_orders_2 @ X8 @ X9 @ X7)
% 0.20/0.46          | ~ (r2_orders_2 @ X8 @ X7 @ X9)
% 0.20/0.46          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.20/0.46          | ~ (l1_orders_2 @ X8)
% 0.20/0.46          | ~ (v5_orders_2 @ X8))),
% 0.20/0.46      inference('cnf', [status(esa)], [t28_orders_2])).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (v5_orders_2 @ sk_A)
% 0.20/0.46          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.46          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.46          | ~ (r2_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.46          | ~ (r2_orders_2 @ sk_A @ X0 @ sk_B))),
% 0.20/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.46  thf('4', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('5', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.46          | ~ (r2_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.46          | ~ (r2_orders_2 @ sk_A @ X0 @ sk_B))),
% 0.20/0.46      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_B)
% 0.20/0.46        | ~ (r2_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.20/0.46      inference('sup-', [status(thm)], ['0', '6'])).
% 0.20/0.46  thf('8', plain, (~ (r2_orders_2 @ sk_A @ sk_B @ sk_B)),
% 0.20/0.46      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.46  thf('9', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('10', plain, ((r2_hidden @ sk_B @ (k1_orders_2 @ sk_A @ sk_C))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(fraenkel_a_2_0_orders_2, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 0.20/0.46         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 0.20/0.46         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.20/0.46       ( ( r2_hidden @ A @ ( a_2_0_orders_2 @ B @ C ) ) <=>
% 0.20/0.46         ( ?[D:$i]:
% 0.20/0.46           ( ( ![E:$i]:
% 0.20/0.46               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.46                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ E @ D ) ) ) ) & 
% 0.20/0.46             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.20/0.46  thf('12', plain,
% 0.20/0.46      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.46         (~ (l1_orders_2 @ X2)
% 0.20/0.46          | ~ (v5_orders_2 @ X2)
% 0.20/0.46          | ~ (v4_orders_2 @ X2)
% 0.20/0.46          | ~ (v3_orders_2 @ X2)
% 0.20/0.46          | (v2_struct_0 @ X2)
% 0.20/0.46          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.20/0.46          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X2))
% 0.20/0.46          | (r2_orders_2 @ X2 @ X4 @ (sk_D @ X3 @ X2 @ X5))
% 0.20/0.46          | ~ (r2_hidden @ X4 @ X3)
% 0.20/0.46          | ~ (r2_hidden @ X5 @ (a_2_0_orders_2 @ X2 @ X3)))),
% 0.20/0.46      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 0.20/0.46  thf('13', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         (~ (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ sk_C))
% 0.20/0.46          | ~ (r2_hidden @ X1 @ sk_C)
% 0.20/0.46          | (r2_orders_2 @ sk_A @ X1 @ (sk_D @ sk_C @ sk_A @ X0))
% 0.20/0.46          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.20/0.46          | (v2_struct_0 @ sk_A)
% 0.20/0.46          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.46          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.46          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.46          | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.46  thf('14', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(d12_orders_2, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.46         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.46       ( ![B:$i]:
% 0.20/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.46           ( ( k1_orders_2 @ A @ B ) = ( a_2_0_orders_2 @ A @ B ) ) ) ) ))).
% 0.20/0.46  thf('15', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.46          | ((k1_orders_2 @ X1 @ X0) = (a_2_0_orders_2 @ X1 @ X0))
% 0.20/0.46          | ~ (l1_orders_2 @ X1)
% 0.20/0.46          | ~ (v5_orders_2 @ X1)
% 0.20/0.46          | ~ (v4_orders_2 @ X1)
% 0.20/0.46          | ~ (v3_orders_2 @ X1)
% 0.20/0.46          | (v2_struct_0 @ X1))),
% 0.20/0.46      inference('cnf', [status(esa)], [d12_orders_2])).
% 0.20/0.46  thf('16', plain,
% 0.20/0.46      (((v2_struct_0 @ sk_A)
% 0.20/0.46        | ~ (v3_orders_2 @ sk_A)
% 0.20/0.46        | ~ (v4_orders_2 @ sk_A)
% 0.20/0.46        | ~ (v5_orders_2 @ sk_A)
% 0.20/0.46        | ~ (l1_orders_2 @ sk_A)
% 0.20/0.46        | ((k1_orders_2 @ sk_A @ sk_C) = (a_2_0_orders_2 @ sk_A @ sk_C)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.46  thf('17', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('18', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('19', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('20', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('21', plain,
% 0.20/0.46      (((v2_struct_0 @ sk_A)
% 0.20/0.46        | ((k1_orders_2 @ sk_A @ sk_C) = (a_2_0_orders_2 @ sk_A @ sk_C)))),
% 0.20/0.46      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 0.20/0.46  thf('22', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('23', plain,
% 0.20/0.46      (((k1_orders_2 @ sk_A @ sk_C) = (a_2_0_orders_2 @ sk_A @ sk_C))),
% 0.20/0.46      inference('clc', [status(thm)], ['21', '22'])).
% 0.20/0.46  thf('24', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('25', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('26', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('27', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('28', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         (~ (r2_hidden @ X0 @ (k1_orders_2 @ sk_A @ sk_C))
% 0.20/0.46          | ~ (r2_hidden @ X1 @ sk_C)
% 0.20/0.46          | (r2_orders_2 @ sk_A @ X1 @ (sk_D @ sk_C @ sk_A @ X0))
% 0.20/0.46          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.20/0.46          | (v2_struct_0 @ sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['13', '23', '24', '25', '26', '27'])).
% 0.20/0.46  thf('29', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         ((v2_struct_0 @ sk_A)
% 0.20/0.46          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.46          | (r2_orders_2 @ sk_A @ X0 @ (sk_D @ sk_C @ sk_A @ sk_B))
% 0.20/0.46          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.20/0.46      inference('sup-', [status(thm)], ['10', '28'])).
% 0.20/0.46  thf('30', plain,
% 0.20/0.46      ((~ (r2_hidden @ sk_B @ sk_C)
% 0.20/0.46        | (r2_orders_2 @ sk_A @ sk_B @ (sk_D @ sk_C @ sk_A @ sk_B))
% 0.20/0.46        | (v2_struct_0 @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['9', '29'])).
% 0.20/0.46  thf('31', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('32', plain,
% 0.20/0.46      (((r2_orders_2 @ sk_A @ sk_B @ (sk_D @ sk_C @ sk_A @ sk_B))
% 0.20/0.46        | (v2_struct_0 @ sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.46  thf('33', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('34', plain, ((r2_orders_2 @ sk_A @ sk_B @ (sk_D @ sk_C @ sk_A @ sk_B))),
% 0.20/0.46      inference('clc', [status(thm)], ['32', '33'])).
% 0.20/0.46  thf('35', plain, ((r2_hidden @ sk_B @ (k1_orders_2 @ sk_A @ sk_C))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('36', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('37', plain,
% 0.20/0.46      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.20/0.46         (~ (l1_orders_2 @ X2)
% 0.20/0.46          | ~ (v5_orders_2 @ X2)
% 0.20/0.46          | ~ (v4_orders_2 @ X2)
% 0.20/0.46          | ~ (v3_orders_2 @ X2)
% 0.20/0.46          | (v2_struct_0 @ X2)
% 0.20/0.46          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.20/0.46          | ((X5) = (sk_D @ X3 @ X2 @ X5))
% 0.20/0.46          | ~ (r2_hidden @ X5 @ (a_2_0_orders_2 @ X2 @ X3)))),
% 0.20/0.46      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 0.20/0.46  thf('38', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ sk_C))
% 0.20/0.46          | ((X0) = (sk_D @ sk_C @ sk_A @ X0))
% 0.20/0.46          | (v2_struct_0 @ sk_A)
% 0.20/0.46          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.46          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.46          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.46          | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.46  thf('39', plain,
% 0.20/0.46      (((k1_orders_2 @ sk_A @ sk_C) = (a_2_0_orders_2 @ sk_A @ sk_C))),
% 0.20/0.46      inference('clc', [status(thm)], ['21', '22'])).
% 0.20/0.46  thf('40', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('41', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('42', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('43', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('44', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (r2_hidden @ X0 @ (k1_orders_2 @ sk_A @ sk_C))
% 0.20/0.46          | ((X0) = (sk_D @ sk_C @ sk_A @ X0))
% 0.20/0.46          | (v2_struct_0 @ sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['38', '39', '40', '41', '42', '43'])).
% 0.20/0.46  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('46', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (((X0) = (sk_D @ sk_C @ sk_A @ X0))
% 0.20/0.46          | ~ (r2_hidden @ X0 @ (k1_orders_2 @ sk_A @ sk_C)))),
% 0.20/0.46      inference('clc', [status(thm)], ['44', '45'])).
% 0.20/0.46  thf('47', plain, (((sk_B) = (sk_D @ sk_C @ sk_A @ sk_B))),
% 0.20/0.46      inference('sup-', [status(thm)], ['35', '46'])).
% 0.20/0.46  thf('48', plain, ((r2_orders_2 @ sk_A @ sk_B @ sk_B)),
% 0.20/0.46      inference('demod', [status(thm)], ['34', '47'])).
% 0.20/0.46  thf('49', plain, ($false), inference('demod', [status(thm)], ['8', '48'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
