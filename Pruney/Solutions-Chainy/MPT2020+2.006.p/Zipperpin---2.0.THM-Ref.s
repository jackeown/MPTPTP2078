%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.clSn4Gs1nt

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   45 (  66 expanded)
%              Number of leaves         :   16 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :  331 (1065 expanded)
%              Number of equality atoms :    9 (  49 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(t19_waybel_9,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
                 => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                        = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                      & ( C = D )
                      & ( v1_tops_2 @ C @ A ) )
                   => ( v1_tops_2 @ D @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( l1_pre_topc @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
                   => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                          = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                        & ( C = D )
                        & ( v1_tops_2 @ C @ A ) )
                     => ( v1_tops_2 @ D @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t19_waybel_9])).

thf('0',plain,(
    ~ ( v1_tops_2 @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    sk_C = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ~ ( v1_tops_2 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_C = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t35_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( v1_tops_2 @ B @ A )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) )
                   => ( ( D = B )
                     => ( v1_tops_2 @ D @ C ) ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) )
      | ~ ( v1_tops_2 @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ( v1_tops_2 @ X4 @ X5 )
      | ( X4 != X2 )
      | ~ ( m1_pre_topc @ X5 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[t35_tops_2])).

thf('8',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_pre_topc @ X5 @ X3 )
      | ( v1_tops_2 @ X2 @ X5 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_tops_2 @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_tops_2 @ sk_C @ X0 )
      | ( v1_tops_2 @ sk_C @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v1_tops_2 @ sk_C @ sk_B )
    | ~ ( v1_tops_2 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('13',plain,(
    ! [X6: $i] :
      ( ( m1_pre_topc @ X6 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( m1_pre_topc @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['12','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('21',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    v1_tops_2 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_tops_2 @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['10','11','24','25'])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['2','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.clSn4Gs1nt
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:36:22 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  % Running portfolio for 600 s
% 0.20/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.36  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 29 iterations in 0.019s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.48  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.48  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.22/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.48  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.22/0.48  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.22/0.48  thf(t19_waybel_9, conjecture,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( l1_pre_topc @ A ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( l1_pre_topc @ B ) =>
% 0.22/0.48           ( ![C:$i]:
% 0.22/0.48             ( ( m1_subset_1 @
% 0.22/0.48                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.48               ( ![D:$i]:
% 0.22/0.48                 ( ( m1_subset_1 @
% 0.22/0.48                     D @ 
% 0.22/0.48                     ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.22/0.48                   ( ( ( ( g1_pre_topc @
% 0.22/0.48                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.22/0.48                         ( g1_pre_topc @
% 0.22/0.48                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.22/0.48                       ( ( C ) = ( D ) ) & ( v1_tops_2 @ C @ A ) ) =>
% 0.22/0.48                     ( v1_tops_2 @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i]:
% 0.22/0.48        ( ( l1_pre_topc @ A ) =>
% 0.22/0.48          ( ![B:$i]:
% 0.22/0.48            ( ( l1_pre_topc @ B ) =>
% 0.22/0.48              ( ![C:$i]:
% 0.22/0.48                ( ( m1_subset_1 @
% 0.22/0.48                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.48                  ( ![D:$i]:
% 0.22/0.48                    ( ( m1_subset_1 @
% 0.22/0.48                        D @ 
% 0.22/0.48                        ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.22/0.48                      ( ( ( ( g1_pre_topc @
% 0.22/0.48                              ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.22/0.48                            ( g1_pre_topc @
% 0.22/0.48                              ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.22/0.48                          ( ( C ) = ( D ) ) & ( v1_tops_2 @ C @ A ) ) =>
% 0.22/0.48                        ( v1_tops_2 @ D @ B ) ) ) ) ) ) ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t19_waybel_9])).
% 0.22/0.48  thf('0', plain, (~ (v1_tops_2 @ sk_D @ sk_B)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('1', plain, (((sk_C) = (sk_D))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('2', plain, (~ (v1_tops_2 @ sk_C @ sk_B)),
% 0.22/0.48      inference('demod', [status(thm)], ['0', '1'])).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_C @ 
% 0.22/0.48        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('4', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_D @ 
% 0.22/0.48        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('5', plain, (((sk_C) = (sk_D))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('6', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_C @ 
% 0.22/0.48        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.22/0.48      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.48  thf(t35_tops_2, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( l1_pre_topc @ A ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( m1_subset_1 @
% 0.22/0.48             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.48           ( ![C:$i]:
% 0.22/0.48             ( ( m1_pre_topc @ C @ A ) =>
% 0.22/0.48               ( ( v1_tops_2 @ B @ A ) =>
% 0.22/0.48                 ( ![D:$i]:
% 0.22/0.48                   ( ( m1_subset_1 @
% 0.22/0.48                       D @ 
% 0.22/0.48                       ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) ) =>
% 0.22/0.48                     ( ( ( D ) = ( B ) ) => ( v1_tops_2 @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.48  thf('7', plain,
% 0.22/0.48      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ X2 @ 
% 0.22/0.48             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3))))
% 0.22/0.48          | ~ (v1_tops_2 @ X2 @ X3)
% 0.22/0.48          | ~ (m1_subset_1 @ X4 @ 
% 0.22/0.48               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5))))
% 0.22/0.48          | (v1_tops_2 @ X4 @ X5)
% 0.22/0.48          | ((X4) != (X2))
% 0.22/0.48          | ~ (m1_pre_topc @ X5 @ X3)
% 0.22/0.48          | ~ (l1_pre_topc @ X3))),
% 0.22/0.48      inference('cnf', [status(esa)], [t35_tops_2])).
% 0.22/0.48  thf('8', plain,
% 0.22/0.48      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.22/0.48         (~ (l1_pre_topc @ X3)
% 0.22/0.48          | ~ (m1_pre_topc @ X5 @ X3)
% 0.22/0.48          | (v1_tops_2 @ X2 @ X5)
% 0.22/0.48          | ~ (m1_subset_1 @ X2 @ 
% 0.22/0.48               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5))))
% 0.22/0.48          | ~ (v1_tops_2 @ X2 @ X3)
% 0.22/0.48          | ~ (m1_subset_1 @ X2 @ 
% 0.22/0.48               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))))),
% 0.22/0.48      inference('simplify', [status(thm)], ['7'])).
% 0.22/0.48  thf('9', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ sk_C @ 
% 0.22/0.48             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.22/0.48          | ~ (v1_tops_2 @ sk_C @ X0)
% 0.22/0.48          | (v1_tops_2 @ sk_C @ sk_B)
% 0.22/0.48          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.22/0.48          | ~ (l1_pre_topc @ X0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['6', '8'])).
% 0.22/0.48  thf('10', plain,
% 0.22/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.48        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.22/0.48        | (v1_tops_2 @ sk_C @ sk_B)
% 0.22/0.48        | ~ (v1_tops_2 @ sk_C @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['3', '9'])).
% 0.22/0.48  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('12', plain,
% 0.22/0.48      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.48         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(t2_tsep_1, axiom,
% 0.22/0.48    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.22/0.48  thf('13', plain,
% 0.22/0.48      (![X6 : $i]: ((m1_pre_topc @ X6 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.22/0.48      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.22/0.48  thf(t65_pre_topc, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( l1_pre_topc @ A ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( l1_pre_topc @ B ) =>
% 0.22/0.48           ( ( m1_pre_topc @ A @ B ) <=>
% 0.22/0.48             ( m1_pre_topc @
% 0.22/0.48               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.22/0.48  thf('14', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         (~ (l1_pre_topc @ X0)
% 0.22/0.48          | ~ (m1_pre_topc @ X1 @ X0)
% 0.22/0.48          | (m1_pre_topc @ X1 @ 
% 0.22/0.48             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.22/0.48          | ~ (l1_pre_topc @ X1))),
% 0.22/0.48      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.22/0.48  thf('15', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (l1_pre_topc @ X0)
% 0.22/0.48          | ~ (l1_pre_topc @ X0)
% 0.22/0.48          | (m1_pre_topc @ X0 @ 
% 0.22/0.48             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.22/0.48          | ~ (l1_pre_topc @ X0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.48  thf('16', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((m1_pre_topc @ X0 @ 
% 0.22/0.48           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.22/0.48          | ~ (l1_pre_topc @ X0))),
% 0.22/0.48      inference('simplify', [status(thm)], ['15'])).
% 0.22/0.48  thf('17', plain,
% 0.22/0.48      (((m1_pre_topc @ sk_B @ 
% 0.22/0.48         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.22/0.48        | ~ (l1_pre_topc @ sk_B))),
% 0.22/0.48      inference('sup+', [status(thm)], ['12', '16'])).
% 0.22/0.48  thf('18', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('19', plain,
% 0.22/0.48      ((m1_pre_topc @ sk_B @ 
% 0.22/0.48        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.22/0.48      inference('demod', [status(thm)], ['17', '18'])).
% 0.22/0.48  thf('20', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         (~ (l1_pre_topc @ X0)
% 0.22/0.48          | ~ (m1_pre_topc @ X1 @ 
% 0.22/0.48               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.22/0.48          | (m1_pre_topc @ X1 @ X0)
% 0.22/0.48          | ~ (l1_pre_topc @ X1))),
% 0.22/0.48      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.22/0.48  thf('21', plain,
% 0.22/0.48      ((~ (l1_pre_topc @ sk_B)
% 0.22/0.48        | (m1_pre_topc @ sk_B @ sk_A)
% 0.22/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.48  thf('22', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('24', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.22/0.48      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.22/0.48  thf('25', plain, ((v1_tops_2 @ sk_C @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('26', plain, ((v1_tops_2 @ sk_C @ sk_B)),
% 0.22/0.48      inference('demod', [status(thm)], ['10', '11', '24', '25'])).
% 0.22/0.48  thf('27', plain, ($false), inference('demod', [status(thm)], ['2', '26'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
