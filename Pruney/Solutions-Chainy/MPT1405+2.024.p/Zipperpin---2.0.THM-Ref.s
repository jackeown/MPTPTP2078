%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tFTPh3FDkm

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:17 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   63 (  81 expanded)
%              Number of leaves         :   25 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :  421 ( 697 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m2_connsp_2_type,type,(
    m2_connsp_2: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t43_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) )
        = ( k2_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X10: $i] :
      ( ( ( k1_tops_1 @ X10 @ ( k2_struct_0 @ X10 ) )
        = ( k2_struct_0 @ X10 ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t43_tops_1])).

thf(rc4_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ? [B: $i] :
          ( ( v1_tops_1 @ B @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[rc4_tops_1])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v1_tops_1 @ X7 @ X8 )
      | ( ( k2_pre_topc @ X8 @ X7 )
        = ( k2_struct_0 @ X8 ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( sk_B @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( v1_tops_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tops_1 @ ( sk_B @ X0 ) @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( sk_B @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X9: $i] :
      ( ( v1_tops_1 @ ( sk_B @ X9 ) @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[rc4_tops_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( sk_B @ X0 ) )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[rc4_tops_1])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X4 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t35_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_connsp_2])).

thf('13',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m2_connsp_2 @ C @ A @ B )
              <=> ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( r1_tarski @ X11 @ ( k1_tops_1 @ X12 @ X13 ) )
      | ( m2_connsp_2 @ X13 @ X12 @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    | ( m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    | ( m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','23'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('25',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('26',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('29',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('30',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('33',plain,(
    r1_tarski @ sk_B_1 @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['24','33','34','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tFTPh3FDkm
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:02:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 59 iterations in 0.033s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.48  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.19/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.48  thf(m2_connsp_2_type, type, m2_connsp_2: $i > $i > $i > $o).
% 0.19/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.48  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.19/0.48  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.19/0.48  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.19/0.48  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.48  thf(t43_tops_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.48       ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.19/0.48  thf('0', plain,
% 0.19/0.48      (![X10 : $i]:
% 0.19/0.48         (((k1_tops_1 @ X10 @ (k2_struct_0 @ X10)) = (k2_struct_0 @ X10))
% 0.19/0.48          | ~ (l1_pre_topc @ X10)
% 0.19/0.48          | ~ (v2_pre_topc @ X10))),
% 0.19/0.48      inference('cnf', [status(esa)], [t43_tops_1])).
% 0.19/0.48  thf(rc4_tops_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( l1_pre_topc @ A ) =>
% 0.19/0.48       ( ?[B:$i]:
% 0.19/0.48         ( ( v1_tops_1 @ B @ A ) & 
% 0.19/0.48           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.19/0.48  thf('1', plain,
% 0.19/0.48      (![X9 : $i]:
% 0.19/0.48         ((m1_subset_1 @ (sk_B @ X9) @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.19/0.48          | ~ (l1_pre_topc @ X9))),
% 0.19/0.48      inference('cnf', [status(esa)], [rc4_tops_1])).
% 0.19/0.48  thf(d3_tops_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( l1_pre_topc @ A ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.48           ( ( v1_tops_1 @ B @ A ) <=>
% 0.19/0.48             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      (![X7 : $i, X8 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.19/0.48          | ~ (v1_tops_1 @ X7 @ X8)
% 0.19/0.48          | ((k2_pre_topc @ X8 @ X7) = (k2_struct_0 @ X8))
% 0.19/0.48          | ~ (l1_pre_topc @ X8))),
% 0.19/0.48      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (l1_pre_topc @ X0)
% 0.19/0.48          | ~ (l1_pre_topc @ X0)
% 0.19/0.48          | ((k2_pre_topc @ X0 @ (sk_B @ X0)) = (k2_struct_0 @ X0))
% 0.19/0.48          | ~ (v1_tops_1 @ (sk_B @ X0) @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.48  thf('4', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (v1_tops_1 @ (sk_B @ X0) @ X0)
% 0.19/0.48          | ((k2_pre_topc @ X0 @ (sk_B @ X0)) = (k2_struct_0 @ X0))
% 0.19/0.48          | ~ (l1_pre_topc @ X0))),
% 0.19/0.48      inference('simplify', [status(thm)], ['3'])).
% 0.19/0.48  thf('5', plain,
% 0.19/0.48      (![X9 : $i]: ((v1_tops_1 @ (sk_B @ X9) @ X9) | ~ (l1_pre_topc @ X9))),
% 0.19/0.48      inference('cnf', [status(esa)], [rc4_tops_1])).
% 0.19/0.48  thf('6', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (l1_pre_topc @ X0)
% 0.19/0.48          | ((k2_pre_topc @ X0 @ (sk_B @ X0)) = (k2_struct_0 @ X0)))),
% 0.19/0.48      inference('clc', [status(thm)], ['4', '5'])).
% 0.19/0.48  thf('7', plain,
% 0.19/0.48      (![X9 : $i]:
% 0.19/0.48         ((m1_subset_1 @ (sk_B @ X9) @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.19/0.48          | ~ (l1_pre_topc @ X9))),
% 0.19/0.48      inference('cnf', [status(esa)], [rc4_tops_1])).
% 0.19/0.48  thf(dt_k2_pre_topc, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( l1_pre_topc @ A ) & 
% 0.19/0.48         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.48       ( m1_subset_1 @
% 0.19/0.48         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.19/0.48  thf('8', plain,
% 0.19/0.48      (![X4 : $i, X5 : $i]:
% 0.19/0.48         (~ (l1_pre_topc @ X4)
% 0.19/0.48          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.19/0.48          | (m1_subset_1 @ (k2_pre_topc @ X4 @ X5) @ 
% 0.19/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X4))))),
% 0.19/0.48      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.19/0.48  thf('9', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (l1_pre_topc @ X0)
% 0.19/0.48          | (m1_subset_1 @ (k2_pre_topc @ X0 @ (sk_B @ X0)) @ 
% 0.19/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.19/0.48          | ~ (l1_pre_topc @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.48  thf('10', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((m1_subset_1 @ (k2_pre_topc @ X0 @ (sk_B @ X0)) @ 
% 0.19/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.19/0.48          | ~ (l1_pre_topc @ X0))),
% 0.19/0.48      inference('simplify', [status(thm)], ['9'])).
% 0.19/0.48  thf('11', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 0.19/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.19/0.48          | ~ (l1_pre_topc @ X0)
% 0.19/0.48          | ~ (l1_pre_topc @ X0))),
% 0.19/0.48      inference('sup+', [status(thm)], ['6', '10'])).
% 0.19/0.48  thf('12', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (l1_pre_topc @ X0)
% 0.19/0.48          | (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 0.19/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.19/0.48      inference('simplify', [status(thm)], ['11'])).
% 0.19/0.48  thf(t35_connsp_2, conjecture,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.48           ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i]:
% 0.19/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.48            ( l1_pre_topc @ A ) ) =>
% 0.19/0.48          ( ![B:$i]:
% 0.19/0.48            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.48              ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t35_connsp_2])).
% 0.19/0.48  thf('13', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(d2_connsp_2, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.48           ( ![C:$i]:
% 0.19/0.48             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.48               ( ( m2_connsp_2 @ C @ A @ B ) <=>
% 0.19/0.48                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.19/0.48  thf('14', plain,
% 0.19/0.48      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.19/0.48          | ~ (r1_tarski @ X11 @ (k1_tops_1 @ X12 @ X13))
% 0.19/0.48          | (m2_connsp_2 @ X13 @ X12 @ X11)
% 0.19/0.48          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.19/0.48          | ~ (l1_pre_topc @ X12)
% 0.19/0.48          | ~ (v2_pre_topc @ X12))),
% 0.19/0.48      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.19/0.48  thf('15', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (v2_pre_topc @ sk_A)
% 0.19/0.48          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.48          | (m2_connsp_2 @ X0 @ sk_A @ sk_B_1)
% 0.19/0.48          | ~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.48  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('18', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.48          | (m2_connsp_2 @ X0 @ sk_A @ sk_B_1)
% 0.19/0.48          | ~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0)))),
% 0.19/0.48      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.19/0.48  thf('19', plain,
% 0.19/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.48        | ~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.19/0.48        | (m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ sk_B_1))),
% 0.19/0.48      inference('sup-', [status(thm)], ['12', '18'])).
% 0.19/0.48  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('21', plain,
% 0.19/0.48      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.19/0.48        | (m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ sk_B_1))),
% 0.19/0.48      inference('demod', [status(thm)], ['19', '20'])).
% 0.19/0.48  thf('22', plain, (~ (m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ sk_B_1)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('23', plain,
% 0.19/0.48      (~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)))),
% 0.19/0.48      inference('clc', [status(thm)], ['21', '22'])).
% 0.19/0.48  thf('24', plain,
% 0.19/0.48      ((~ (r1_tarski @ sk_B_1 @ (k2_struct_0 @ sk_A))
% 0.19/0.48        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['0', '23'])).
% 0.19/0.48  thf(d3_struct_0, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.19/0.48  thf('25', plain,
% 0.19/0.48      (![X3 : $i]:
% 0.19/0.48         (((k2_struct_0 @ X3) = (u1_struct_0 @ X3)) | ~ (l1_struct_0 @ X3))),
% 0.19/0.48      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.48  thf('26', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('27', plain,
% 0.19/0.48      (((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.19/0.48        | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.48      inference('sup+', [status(thm)], ['25', '26'])).
% 0.19/0.48  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(dt_l1_pre_topc, axiom,
% 0.19/0.48    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.19/0.48  thf('29', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.19/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.48  thf('30', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.48      inference('sup-', [status(thm)], ['28', '29'])).
% 0.19/0.48  thf('31', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.19/0.48      inference('demod', [status(thm)], ['27', '30'])).
% 0.19/0.48  thf(t3_subset, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.48  thf('32', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.48  thf('33', plain, ((r1_tarski @ sk_B_1 @ (k2_struct_0 @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['31', '32'])).
% 0.19/0.48  thf('34', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('36', plain, ($false),
% 0.19/0.48      inference('demod', [status(thm)], ['24', '33', '34', '35'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
