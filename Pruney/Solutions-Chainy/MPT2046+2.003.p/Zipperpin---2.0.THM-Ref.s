%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hbzF4MKSML

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   53 (  76 expanded)
%              Number of leaves         :   18 (  31 expanded)
%              Depth                    :   15
%              Number of atoms          :  535 ( 921 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_yellow19_type,type,(
    k1_yellow19: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_waybel_7_type,type,(
    r2_waybel_7: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t5_yellow19,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r2_waybel_7 @ A @ ( k1_yellow19 @ A @ B ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( r2_waybel_7 @ A @ ( k1_yellow19 @ A @ B ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t5_yellow19])).

thf('0',plain,(
    ~ ( r2_waybel_7 @ sk_A @ ( k1_yellow19 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_waybel_7,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r2_waybel_7 @ A @ B @ C )
        <=> ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v3_pre_topc @ D @ A )
                  & ( r2_hidden @ C @ D ) )
               => ( r2_hidden @ D @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X3 @ ( sk_D @ X3 @ X4 @ X5 ) )
      | ( r2_waybel_7 @ X5 @ X4 @ X3 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_waybel_7])).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v3_pre_topc @ ( sk_D @ X3 @ X4 @ X5 ) @ X5 )
      | ( r2_waybel_7 @ X5 @ X4 @ X3 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_waybel_7])).

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X3 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( r2_waybel_7 @ X5 @ X4 @ X3 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_waybel_7])).

thf(t5_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r2_hidden @ C @ B ) )
               => ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v3_pre_topc @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ X0 )
      | ( m1_connsp_2 @ X0 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t5_connsp_2])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_waybel_7 @ X0 @ X1 @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X0 ) )
      | ( m1_connsp_2 @ ( sk_D @ X2 @ X1 @ X0 ) @ X0 @ X3 )
      | ~ ( r2_hidden @ X3 @ ( sk_D @ X2 @ X1 @ X0 ) )
      | ~ ( v3_pre_topc @ ( sk_D @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v3_pre_topc @ ( sk_D @ X2 @ X1 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ X3 @ ( sk_D @ X2 @ X1 @ X0 ) )
      | ( m1_connsp_2 @ ( sk_D @ X2 @ X1 @ X0 ) @ X0 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ( r2_waybel_7 @ X0 @ X1 @ X2 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_waybel_7 @ X0 @ X1 @ X2 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_waybel_7 @ X0 @ X1 @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X0 ) )
      | ( m1_connsp_2 @ ( sk_D @ X2 @ X1 @ X0 ) @ X0 @ X3 )
      | ~ ( r2_hidden @ X3 @ ( sk_D @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( sk_D @ X2 @ X1 @ X0 ) )
      | ( m1_connsp_2 @ ( sk_D @ X2 @ X1 @ X0 ) @ X0 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ( r2_waybel_7 @ X0 @ X1 @ X2 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_waybel_7 @ X0 @ X1 @ X2 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_waybel_7 @ X0 @ X1 @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( m1_connsp_2 @ ( sk_D @ X2 @ X1 @ X0 ) @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_connsp_2 @ ( sk_D @ X2 @ X1 @ X0 ) @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ( r2_waybel_7 @ X0 @ X1 @ X2 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_waybel_7 @ sk_A @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ ( sk_D @ sk_B @ X0 @ sk_A ) @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_waybel_7 @ sk_A @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ ( sk_D @ sk_B @ X0 @ sk_A ) @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( m1_connsp_2 @ ( sk_D @ sk_B @ X0 @ sk_A ) @ sk_A @ sk_B )
      | ( r2_waybel_7 @ sk_A @ X0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_yellow19,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( r2_hidden @ C @ ( k1_yellow19 @ A @ B ) )
            <=> ( m1_connsp_2 @ C @ A @ B ) ) ) ) )).

thf('19',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_connsp_2 @ X11 @ X9 @ X8 )
      | ( r2_hidden @ X11 @ ( k1_yellow19 @ X9 @ X8 ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_yellow19])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B )
      | ( r2_hidden @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_waybel_7 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_A ) @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','25'])).

thf('27',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X3 @ X4 @ X5 ) @ X4 )
      | ( r2_waybel_7 @ X5 @ X4 @ X3 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_waybel_7])).

thf('28',plain,
    ( ( r2_waybel_7 @ sk_A @ ( k1_yellow19 @ sk_A @ sk_B ) @ sk_B )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_waybel_7 @ sk_A @ ( k1_yellow19 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( r2_waybel_7 @ sk_A @ ( k1_yellow19 @ sk_A @ sk_B ) @ sk_B )
    | ( r2_waybel_7 @ sk_A @ ( k1_yellow19 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    r2_waybel_7 @ sk_A @ ( k1_yellow19 @ sk_A @ sk_B ) @ sk_B ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['0','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hbzF4MKSML
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:32:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 19 iterations in 0.018s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(k1_yellow19_type, type, k1_yellow19: $i > $i > $i).
% 0.20/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.47  thf(r2_waybel_7_type, type, r2_waybel_7: $i > $i > $i > $o).
% 0.20/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.47  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.47  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.47  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(t5_yellow19, conjecture,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.47           ( r2_waybel_7 @ A @ ( k1_yellow19 @ A @ B ) @ B ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]:
% 0.20/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.47            ( l1_pre_topc @ A ) ) =>
% 0.20/0.47          ( ![B:$i]:
% 0.20/0.47            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.47              ( r2_waybel_7 @ A @ ( k1_yellow19 @ A @ B ) @ B ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t5_yellow19])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      (~ (r2_waybel_7 @ sk_A @ (k1_yellow19 @ sk_A @ sk_B) @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(d5_waybel_7, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.47       ( ![B:$i,C:$i]:
% 0.20/0.47         ( ( r2_waybel_7 @ A @ B @ C ) <=>
% 0.20/0.47           ( ![D:$i]:
% 0.20/0.47             ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47               ( ( ( v3_pre_topc @ D @ A ) & ( r2_hidden @ C @ D ) ) =>
% 0.20/0.47                 ( r2_hidden @ D @ B ) ) ) ) ) ) ))).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.47         ((r2_hidden @ X3 @ (sk_D @ X3 @ X4 @ X5))
% 0.20/0.47          | (r2_waybel_7 @ X5 @ X4 @ X3)
% 0.20/0.47          | ~ (l1_pre_topc @ X5)
% 0.20/0.47          | ~ (v2_pre_topc @ X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [d5_waybel_7])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.47         ((v3_pre_topc @ (sk_D @ X3 @ X4 @ X5) @ X5)
% 0.20/0.47          | (r2_waybel_7 @ X5 @ X4 @ X3)
% 0.20/0.47          | ~ (l1_pre_topc @ X5)
% 0.20/0.47          | ~ (v2_pre_topc @ X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [d5_waybel_7])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.47         ((m1_subset_1 @ (sk_D @ X3 @ X4 @ X5) @ 
% 0.20/0.47           (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.20/0.47          | (r2_waybel_7 @ X5 @ X4 @ X3)
% 0.20/0.47          | ~ (l1_pre_topc @ X5)
% 0.20/0.47          | ~ (v2_pre_topc @ X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [d5_waybel_7])).
% 0.20/0.47  thf(t5_connsp_2, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47           ( ![C:$i]:
% 0.20/0.47             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.47               ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 0.20/0.47                 ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ))).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.47          | ~ (v3_pre_topc @ X0 @ X1)
% 0.20/0.47          | ~ (r2_hidden @ X2 @ X0)
% 0.20/0.47          | (m1_connsp_2 @ X0 @ X1 @ X2)
% 0.20/0.47          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.47          | ~ (l1_pre_topc @ X1)
% 0.20/0.47          | ~ (v2_pre_topc @ X1)
% 0.20/0.47          | (v2_struct_0 @ X1))),
% 0.20/0.47      inference('cnf', [status(esa)], [t5_connsp_2])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.47         (~ (v2_pre_topc @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | (r2_waybel_7 @ X0 @ X1 @ X2)
% 0.20/0.47          | (v2_struct_0 @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X0))
% 0.20/0.47          | (m1_connsp_2 @ (sk_D @ X2 @ X1 @ X0) @ X0 @ X3)
% 0.20/0.47          | ~ (r2_hidden @ X3 @ (sk_D @ X2 @ X1 @ X0))
% 0.20/0.47          | ~ (v3_pre_topc @ (sk_D @ X2 @ X1 @ X0) @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.47         (~ (v3_pre_topc @ (sk_D @ X2 @ X1 @ X0) @ X0)
% 0.20/0.47          | ~ (r2_hidden @ X3 @ (sk_D @ X2 @ X1 @ X0))
% 0.20/0.47          | (m1_connsp_2 @ (sk_D @ X2 @ X1 @ X0) @ X0 @ X3)
% 0.20/0.47          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X0))
% 0.20/0.47          | (v2_struct_0 @ X0)
% 0.20/0.47          | (r2_waybel_7 @ X0 @ X1 @ X2)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.47         (~ (v2_pre_topc @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | (r2_waybel_7 @ X0 @ X1 @ X2)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | (r2_waybel_7 @ X0 @ X1 @ X2)
% 0.20/0.47          | (v2_struct_0 @ X0)
% 0.20/0.47          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X0))
% 0.20/0.47          | (m1_connsp_2 @ (sk_D @ X2 @ X1 @ X0) @ X0 @ X3)
% 0.20/0.47          | ~ (r2_hidden @ X3 @ (sk_D @ X2 @ X1 @ X0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['3', '7'])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X3 @ (sk_D @ X2 @ X1 @ X0))
% 0.20/0.47          | (m1_connsp_2 @ (sk_D @ X2 @ X1 @ X0) @ X0 @ X3)
% 0.20/0.47          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X0))
% 0.20/0.47          | (v2_struct_0 @ X0)
% 0.20/0.47          | (r2_waybel_7 @ X0 @ X1 @ X2)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (v2_pre_topc @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | (r2_waybel_7 @ X0 @ X1 @ X2)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | (r2_waybel_7 @ X0 @ X1 @ X2)
% 0.20/0.47          | (v2_struct_0 @ X0)
% 0.20/0.47          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.47          | (m1_connsp_2 @ (sk_D @ X2 @ X1 @ X0) @ X0 @ X2))),
% 0.20/0.47      inference('sup-', [status(thm)], ['2', '9'])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         ((m1_connsp_2 @ (sk_D @ X2 @ X1 @ X0) @ X0 @ X2)
% 0.20/0.47          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.47          | (v2_struct_0 @ X0)
% 0.20/0.47          | (r2_waybel_7 @ X0 @ X1 @ X2)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (v2_pre_topc @ sk_A)
% 0.20/0.47          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.47          | (r2_waybel_7 @ sk_A @ X0 @ sk_B)
% 0.20/0.47          | (v2_struct_0 @ sk_A)
% 0.20/0.47          | (m1_connsp_2 @ (sk_D @ sk_B @ X0 @ sk_A) @ sk_A @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '11'])).
% 0.20/0.47  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r2_waybel_7 @ sk_A @ X0 @ sk_B)
% 0.20/0.47          | (v2_struct_0 @ sk_A)
% 0.20/0.47          | (m1_connsp_2 @ (sk_D @ sk_B @ X0 @ sk_A) @ sk_A @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.20/0.47  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((m1_connsp_2 @ (sk_D @ sk_B @ X0 @ sk_A) @ sk_A @ sk_B)
% 0.20/0.47          | (r2_waybel_7 @ sk_A @ X0 @ sk_B))),
% 0.20/0.47      inference('clc', [status(thm)], ['15', '16'])).
% 0.20/0.47  thf('18', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t3_yellow19, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.47           ( ![C:$i]:
% 0.20/0.47             ( ( r2_hidden @ C @ ( k1_yellow19 @ A @ B ) ) <=>
% 0.20/0.47               ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ))).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      (![X8 : $i, X9 : $i, X11 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.20/0.47          | ~ (m1_connsp_2 @ X11 @ X9 @ X8)
% 0.20/0.47          | (r2_hidden @ X11 @ (k1_yellow19 @ X9 @ X8))
% 0.20/0.47          | ~ (l1_pre_topc @ X9)
% 0.20/0.47          | ~ (v2_pre_topc @ X9)
% 0.20/0.47          | (v2_struct_0 @ X9))),
% 0.20/0.47      inference('cnf', [status(esa)], [t3_yellow19])).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_struct_0 @ sk_A)
% 0.20/0.47          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.47          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.47          | (r2_hidden @ X0 @ (k1_yellow19 @ sk_A @ sk_B))
% 0.20/0.47          | ~ (m1_connsp_2 @ X0 @ sk_A @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.47  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_struct_0 @ sk_A)
% 0.20/0.47          | (r2_hidden @ X0 @ (k1_yellow19 @ sk_A @ sk_B))
% 0.20/0.47          | ~ (m1_connsp_2 @ X0 @ sk_A @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.20/0.47  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (m1_connsp_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.47          | (r2_hidden @ X0 @ (k1_yellow19 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('clc', [status(thm)], ['23', '24'])).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r2_waybel_7 @ sk_A @ X0 @ sk_B)
% 0.20/0.47          | (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_A) @ 
% 0.20/0.47             (k1_yellow19 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['17', '25'])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.47         (~ (r2_hidden @ (sk_D @ X3 @ X4 @ X5) @ X4)
% 0.20/0.47          | (r2_waybel_7 @ X5 @ X4 @ X3)
% 0.20/0.47          | ~ (l1_pre_topc @ X5)
% 0.20/0.47          | ~ (v2_pre_topc @ X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [d5_waybel_7])).
% 0.20/0.47  thf('28', plain,
% 0.20/0.47      (((r2_waybel_7 @ sk_A @ (k1_yellow19 @ sk_A @ sk_B) @ sk_B)
% 0.20/0.47        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.47        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.47        | (r2_waybel_7 @ sk_A @ (k1_yellow19 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.47  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('31', plain,
% 0.20/0.47      (((r2_waybel_7 @ sk_A @ (k1_yellow19 @ sk_A @ sk_B) @ sk_B)
% 0.20/0.47        | (r2_waybel_7 @ sk_A @ (k1_yellow19 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.20/0.47  thf('32', plain, ((r2_waybel_7 @ sk_A @ (k1_yellow19 @ sk_A @ sk_B) @ sk_B)),
% 0.20/0.47      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.47  thf('33', plain, ($false), inference('demod', [status(thm)], ['0', '32'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
