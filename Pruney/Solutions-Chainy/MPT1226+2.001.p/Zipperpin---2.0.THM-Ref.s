%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.v3tzj8yENM

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 (  80 expanded)
%              Number of leaves         :   15 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :  465 (1271 expanded)
%              Number of equality atoms :   18 (  22 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t35_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v4_pre_topc @ B @ A )
                  & ( v4_pre_topc @ C @ A ) )
               => ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v4_pre_topc @ B @ A )
                    & ( v4_pre_topc @ C @ A ) )
                 => ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_tops_1])).

thf('0',plain,(
    ~ ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t34_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v4_pre_topc @ B @ A )
                  & ( v4_pre_topc @ C @ A ) )
               => ( ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) )
                  = ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( v4_pre_topc @ X5 @ X6 )
      | ~ ( v4_pre_topc @ X7 @ X6 )
      | ( ( k2_pre_topc @ X6 @ ( k9_subset_1 @ ( u1_struct_0 @ X6 ) @ X5 @ X7 ) )
        = ( k9_subset_1 @ ( u1_struct_0 @ X6 ) @ ( k2_pre_topc @ X6 @ X5 ) @ ( k2_pre_topc @ X6 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t34_tops_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ X0 ) ) )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( v4_pre_topc @ X3 @ X4 )
      | ( ( k2_pre_topc @ X4 @ X3 )
        = X3 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('8',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ X0 ) ) )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','11','12'])).

thf('14',plain,
    ( ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['1','13'])).

thf('15',plain,(
    v4_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( v4_pre_topc @ X3 @ X4 )
      | ( ( k2_pre_topc @ X4 @ X3 )
        = X3 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_C )
      = sk_C )
    | ~ ( v4_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v4_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k2_pre_topc @ sk_A @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['14','15','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X2 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( v2_pre_topc @ X4 )
      | ( ( k2_pre_topc @ X4 @ X3 )
       != X3 )
      | ( v4_pre_topc @ X3 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) )
       != ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) )
       != ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C )
     != ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) )
    | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['22','30'])).

thf('32',plain,(
    v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['0','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.v3tzj8yENM
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:29:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 35 iterations in 0.038s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.20/0.48  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.48  thf(t35_tops_1, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48               ( ( ( v4_pre_topc @ B @ A ) & ( v4_pre_topc @ C @ A ) ) =>
% 0.20/0.48                 ( v4_pre_topc @
% 0.20/0.48                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48          ( ![B:$i]:
% 0.20/0.48            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48              ( ![C:$i]:
% 0.20/0.48                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48                  ( ( ( v4_pre_topc @ B @ A ) & ( v4_pre_topc @ C @ A ) ) =>
% 0.20/0.48                    ( v4_pre_topc @
% 0.20/0.48                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t35_tops_1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (~ (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.20/0.48          sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t34_tops_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48               ( ( ( v4_pre_topc @ B @ A ) & ( v4_pre_topc @ C @ A ) ) =>
% 0.20/0.48                 ( ( k2_pre_topc @
% 0.20/0.48                     A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) =
% 0.20/0.48                   ( k9_subset_1 @
% 0.20/0.48                     ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.20/0.48                     ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.20/0.48          | ~ (v4_pre_topc @ X5 @ X6)
% 0.20/0.48          | ~ (v4_pre_topc @ X7 @ X6)
% 0.20/0.48          | ((k2_pre_topc @ X6 @ (k9_subset_1 @ (u1_struct_0 @ X6) @ X5 @ X7))
% 0.20/0.48              = (k9_subset_1 @ (u1_struct_0 @ X6) @ (k2_pre_topc @ X6 @ X5) @ 
% 0.20/0.48                 (k2_pre_topc @ X6 @ X7)))
% 0.20/0.48          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.20/0.48          | ~ (l1_pre_topc @ X6))),
% 0.20/0.48      inference('cnf', [status(esa)], [t34_tops_1])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ sk_A)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48          | ((k2_pre_topc @ sk_A @ 
% 0.20/0.48              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))
% 0.20/0.48              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48                 (k2_pre_topc @ sk_A @ sk_B) @ (k2_pre_topc @ sk_A @ X0)))
% 0.20/0.48          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.48          | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t52_pre_topc, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.20/0.48             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.20/0.48               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.48          | ~ (v4_pre_topc @ X3 @ X4)
% 0.20/0.48          | ((k2_pre_topc @ X4 @ X3) = (X3))
% 0.20/0.48          | ~ (l1_pre_topc @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.20/0.48        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.48  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('10', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('11', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.20/0.48  thf('12', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48          | ((k2_pre_topc @ sk_A @ 
% 0.20/0.48              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))
% 0.20/0.48              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.48                 (k2_pre_topc @ sk_A @ X0)))
% 0.20/0.48          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['4', '5', '11', '12'])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      ((~ (v4_pre_topc @ sk_C @ sk_A)
% 0.20/0.48        | ((k2_pre_topc @ sk_A @ 
% 0.20/0.48            (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))
% 0.20/0.48            = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.48               (k2_pre_topc @ sk_A @ sk_C))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '13'])).
% 0.20/0.48  thf('15', plain, ((v4_pre_topc @ sk_C @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.48          | ~ (v4_pre_topc @ X3 @ X4)
% 0.20/0.48          | ((k2_pre_topc @ X4 @ X3) = (X3))
% 0.20/0.48          | ~ (l1_pre_topc @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | ((k2_pre_topc @ sk_A @ sk_C) = (sk_C))
% 0.20/0.48        | ~ (v4_pre_topc @ sk_C @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.48  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('20', plain, ((v4_pre_topc @ sk_C @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('21', plain, (((k2_pre_topc @ sk_A @ sk_C) = (sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (((k2_pre_topc @ sk_A @ 
% 0.20/0.48         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))
% 0.20/0.48         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['14', '15', '21'])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(dt_k9_subset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.48       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         ((m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ X2) @ (k1_zfmisc_1 @ X0))
% 0.20/0.48          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C) @ 
% 0.20/0.48          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.48          | ~ (v2_pre_topc @ X4)
% 0.20/0.48          | ((k2_pre_topc @ X4 @ X3) != (X3))
% 0.20/0.48          | (v4_pre_topc @ X3 @ X4)
% 0.20/0.48          | ~ (l1_pre_topc @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ sk_A)
% 0.20/0.48          | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C) @ 
% 0.20/0.48             sk_A)
% 0.20/0.48          | ((k2_pre_topc @ sk_A @ 
% 0.20/0.48              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C))
% 0.20/0.48              != (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C))
% 0.20/0.48          | ~ (v2_pre_topc @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.48  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C) @ 
% 0.20/0.48           sk_A)
% 0.20/0.48          | ((k2_pre_topc @ sk_A @ 
% 0.20/0.48              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C))
% 0.20/0.48              != (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)))),
% 0.20/0.48      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 0.20/0.48          != (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))
% 0.20/0.48        | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.20/0.48           sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['22', '30'])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      ((v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ sk_A)),
% 0.20/0.48      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.48  thf('33', plain, ($false), inference('demod', [status(thm)], ['0', '32'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
