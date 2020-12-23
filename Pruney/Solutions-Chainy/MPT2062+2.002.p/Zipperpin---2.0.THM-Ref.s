%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.k1e5VsV00I

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   49 (  65 expanded)
%              Number of leaves         :   19 (  29 expanded)
%              Depth                    :   14
%              Number of atoms          :  422 ( 714 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r2_waybel_7_type,type,(
    r2_waybel_7: $i > $i > $i > $o )).

thf(t22_yellow19,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i,C: $i,D: $i] :
          ( ( ( r1_tarski @ B @ C )
            & ( r2_waybel_7 @ A @ B @ D ) )
         => ( r2_waybel_7 @ A @ C @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i,C: $i,D: $i] :
            ( ( ( r1_tarski @ B @ C )
              & ( r2_waybel_7 @ A @ B @ D ) )
           => ( r2_waybel_7 @ A @ C @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t22_yellow19])).

thf('0',plain,(
    ~ ( r2_waybel_7 @ sk_A @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_waybel_7 @ sk_A @ sk_B @ sk_D_1 ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X6 @ ( sk_D @ X6 @ X7 @ X8 ) )
      | ( r2_waybel_7 @ X8 @ X7 @ X6 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_waybel_7])).

thf('3',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v3_pre_topc @ ( sk_D @ X6 @ X7 @ X8 ) @ X8 )
      | ( r2_waybel_7 @ X8 @ X7 @ X6 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_waybel_7])).

thf('4',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X6 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( r2_waybel_7 @ X8 @ X7 @ X6 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_waybel_7])).

thf('5',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_waybel_7 @ X8 @ X7 @ X9 )
      | ~ ( v3_pre_topc @ X10 @ X8 )
      | ~ ( r2_hidden @ X9 @ X10 )
      | ( r2_hidden @ X10 @ X7 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_waybel_7])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_waybel_7 @ X0 @ X1 @ X2 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X3 )
      | ~ ( r2_hidden @ X4 @ ( sk_D @ X2 @ X1 @ X0 ) )
      | ~ ( v3_pre_topc @ ( sk_D @ X2 @ X1 @ X0 ) @ X0 )
      | ~ ( r2_waybel_7 @ X0 @ X3 @ X4 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_waybel_7 @ X0 @ X3 @ X4 )
      | ~ ( v3_pre_topc @ ( sk_D @ X2 @ X1 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ X4 @ ( sk_D @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X3 )
      | ( r2_waybel_7 @ X0 @ X1 @ X2 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_waybel_7 @ X0 @ X1 @ X2 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_waybel_7 @ X0 @ X1 @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X3 )
      | ~ ( r2_hidden @ X4 @ ( sk_D @ X2 @ X1 @ X0 ) )
      | ~ ( r2_waybel_7 @ X0 @ X3 @ X4 ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_waybel_7 @ X0 @ X3 @ X4 )
      | ~ ( r2_hidden @ X4 @ ( sk_D @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X3 )
      | ( r2_waybel_7 @ X0 @ X1 @ X2 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_waybel_7 @ X0 @ X1 @ X2 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_waybel_7 @ X0 @ X1 @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X3 )
      | ~ ( r2_waybel_7 @ X0 @ X3 @ X2 ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_waybel_7 @ X0 @ X3 @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X3 )
      | ( r2_waybel_7 @ X0 @ X1 @ X2 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_waybel_7 @ sk_A @ X0 @ sk_D_1 )
      | ( r2_hidden @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_waybel_7 @ sk_A @ X0 @ sk_D_1 )
      | ( r2_hidden @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_waybel_7 @ sk_A @ X0 @ sk_D_1 )
      | ( r2_hidden @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X6 @ X7 @ X8 ) @ X7 )
      | ( r2_waybel_7 @ X8 @ X7 @ X6 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_waybel_7])).

thf('23',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_C @ sk_D_1 )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_waybel_7 @ sk_A @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_C @ sk_D_1 )
    | ( r2_waybel_7 @ sk_A @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    r2_waybel_7 @ sk_A @ sk_C @ sk_D_1 ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    $false ),
    inference(demod,[status(thm)],['0','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.k1e5VsV00I
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:43:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 27 iterations in 0.017s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.47  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(r2_waybel_7_type, type, r2_waybel_7: $i > $i > $i > $o).
% 0.20/0.47  thf(t22_yellow19, conjecture,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.47       ( ![B:$i,C:$i,D:$i]:
% 0.20/0.47         ( ( ( r1_tarski @ B @ C ) & ( r2_waybel_7 @ A @ B @ D ) ) =>
% 0.20/0.47           ( r2_waybel_7 @ A @ C @ D ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]:
% 0.20/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.47            ( l1_pre_topc @ A ) ) =>
% 0.20/0.47          ( ![B:$i,C:$i,D:$i]:
% 0.20/0.47            ( ( ( r1_tarski @ B @ C ) & ( r2_waybel_7 @ A @ B @ D ) ) =>
% 0.20/0.47              ( r2_waybel_7 @ A @ C @ D ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t22_yellow19])).
% 0.20/0.47  thf('0', plain, (~ (r2_waybel_7 @ sk_A @ sk_C @ sk_D_1)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain, ((r2_waybel_7 @ sk_A @ sk_B @ sk_D_1)),
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
% 0.20/0.47      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.47         ((r2_hidden @ X6 @ (sk_D @ X6 @ X7 @ X8))
% 0.20/0.47          | (r2_waybel_7 @ X8 @ X7 @ X6)
% 0.20/0.47          | ~ (l1_pre_topc @ X8)
% 0.20/0.47          | ~ (v2_pre_topc @ X8))),
% 0.20/0.47      inference('cnf', [status(esa)], [d5_waybel_7])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.47         ((v3_pre_topc @ (sk_D @ X6 @ X7 @ X8) @ X8)
% 0.20/0.47          | (r2_waybel_7 @ X8 @ X7 @ X6)
% 0.20/0.47          | ~ (l1_pre_topc @ X8)
% 0.20/0.47          | ~ (v2_pre_topc @ X8))),
% 0.20/0.47      inference('cnf', [status(esa)], [d5_waybel_7])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.47         ((m1_subset_1 @ (sk_D @ X6 @ X7 @ X8) @ 
% 0.20/0.47           (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.47          | (r2_waybel_7 @ X8 @ X7 @ X6)
% 0.20/0.47          | ~ (l1_pre_topc @ X8)
% 0.20/0.47          | ~ (v2_pre_topc @ X8))),
% 0.20/0.47      inference('cnf', [status(esa)], [d5_waybel_7])).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.47         (~ (r2_waybel_7 @ X8 @ X7 @ X9)
% 0.20/0.47          | ~ (v3_pre_topc @ X10 @ X8)
% 0.20/0.47          | ~ (r2_hidden @ X9 @ X10)
% 0.20/0.47          | (r2_hidden @ X10 @ X7)
% 0.20/0.47          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.47          | ~ (l1_pre_topc @ X8)
% 0.20/0.47          | ~ (v2_pre_topc @ X8))),
% 0.20/0.47      inference('cnf', [status(esa)], [d5_waybel_7])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.47         (~ (v2_pre_topc @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | (r2_waybel_7 @ X0 @ X1 @ X2)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X3)
% 0.20/0.47          | ~ (r2_hidden @ X4 @ (sk_D @ X2 @ X1 @ X0))
% 0.20/0.47          | ~ (v3_pre_topc @ (sk_D @ X2 @ X1 @ X0) @ X0)
% 0.20/0.47          | ~ (r2_waybel_7 @ X0 @ X3 @ X4))),
% 0.20/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.47         (~ (r2_waybel_7 @ X0 @ X3 @ X4)
% 0.20/0.47          | ~ (v3_pre_topc @ (sk_D @ X2 @ X1 @ X0) @ X0)
% 0.20/0.47          | ~ (r2_hidden @ X4 @ (sk_D @ X2 @ X1 @ X0))
% 0.20/0.47          | (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X3)
% 0.20/0.47          | (r2_waybel_7 @ X0 @ X1 @ X2)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.47         (~ (v2_pre_topc @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | (r2_waybel_7 @ X0 @ X1 @ X2)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | (r2_waybel_7 @ X0 @ X1 @ X2)
% 0.20/0.47          | (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X3)
% 0.20/0.47          | ~ (r2_hidden @ X4 @ (sk_D @ X2 @ X1 @ X0))
% 0.20/0.47          | ~ (r2_waybel_7 @ X0 @ X3 @ X4))),
% 0.20/0.47      inference('sup-', [status(thm)], ['3', '7'])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.47         (~ (r2_waybel_7 @ X0 @ X3 @ X4)
% 0.20/0.47          | ~ (r2_hidden @ X4 @ (sk_D @ X2 @ X1 @ X0))
% 0.20/0.47          | (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X3)
% 0.20/0.47          | (r2_waybel_7 @ X0 @ X1 @ X2)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.47         (~ (v2_pre_topc @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | (r2_waybel_7 @ X0 @ X1 @ X2)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | (r2_waybel_7 @ X0 @ X1 @ X2)
% 0.20/0.47          | (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X3)
% 0.20/0.47          | ~ (r2_waybel_7 @ X0 @ X3 @ X2))),
% 0.20/0.47      inference('sup-', [status(thm)], ['2', '9'])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.47         (~ (r2_waybel_7 @ X0 @ X3 @ X2)
% 0.20/0.47          | (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X3)
% 0.20/0.47          | (r2_waybel_7 @ X0 @ X1 @ X2)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (v2_pre_topc @ sk_A)
% 0.20/0.47          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.47          | (r2_waybel_7 @ sk_A @ X0 @ sk_D_1)
% 0.20/0.47          | (r2_hidden @ (sk_D @ sk_D_1 @ X0 @ sk_A) @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '11'])).
% 0.20/0.47  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r2_waybel_7 @ sk_A @ X0 @ sk_D_1)
% 0.20/0.47          | (r2_hidden @ (sk_D @ sk_D_1 @ X0 @ sk_A) @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.20/0.47  thf('16', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t3_subset, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (![X3 : $i, X5 : $i]:
% 0.20/0.47         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.47  thf('18', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.47  thf(l3_subset_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.47          | (r2_hidden @ X0 @ X2)
% 0.20/0.47          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.20/0.47      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r2_waybel_7 @ sk_A @ X0 @ sk_D_1)
% 0.20/0.47          | (r2_hidden @ (sk_D @ sk_D_1 @ X0 @ sk_A) @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['15', '20'])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.47         (~ (r2_hidden @ (sk_D @ X6 @ X7 @ X8) @ X7)
% 0.20/0.47          | (r2_waybel_7 @ X8 @ X7 @ X6)
% 0.20/0.47          | ~ (l1_pre_topc @ X8)
% 0.20/0.47          | ~ (v2_pre_topc @ X8))),
% 0.20/0.47      inference('cnf', [status(esa)], [d5_waybel_7])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      (((r2_waybel_7 @ sk_A @ sk_C @ sk_D_1)
% 0.20/0.47        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.47        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.47        | (r2_waybel_7 @ sk_A @ sk_C @ sk_D_1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.47  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      (((r2_waybel_7 @ sk_A @ sk_C @ sk_D_1)
% 0.20/0.47        | (r2_waybel_7 @ sk_A @ sk_C @ sk_D_1))),
% 0.20/0.47      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.20/0.47  thf('27', plain, ((r2_waybel_7 @ sk_A @ sk_C @ sk_D_1)),
% 0.20/0.47      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.47  thf('28', plain, ($false), inference('demod', [status(thm)], ['0', '27'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
