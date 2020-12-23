%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.y5KP1g7S8J

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:10 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   64 (  79 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :   12
%              Number of atoms          :  329 ( 756 expanded)
%              Number of equality atoms :    8 (  22 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t15_tmap_1,conjecture,(
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
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) )
                   => ? [E: $i] :
                        ( ( E = D )
                        & ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
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
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) )
                     => ? [E: $i] :
                          ( ( E = D )
                          & ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t15_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('3',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( l1_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['3','8'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('13',plain,
    ( ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    = ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( r2_hidden @ sk_D_1 @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( m1_subset_1 @ sk_D_1 @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['13','21'])).

thf('23',plain,(
    ! [X21: $i] :
      ( ( X21 != sk_D_1 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','24'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('26',plain,(
    ! [X18: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('27',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( l1_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['30','31'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('33',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('34',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v2_struct_0 @ sk_B ),
    inference(demod,[status(thm)],['27','34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['0','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.y5KP1g7S8J
% 0.13/0.36  % Computer   : n001.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 13:10:30 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 51 iterations in 0.024s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.50  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.22/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.50  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(t15_tmap_1, conjecture,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.22/0.50           ( ![C:$i]:
% 0.22/0.50             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.50               ( ( m1_pre_topc @ B @ C ) =>
% 0.22/0.50                 ( ![D:$i]:
% 0.22/0.50                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.22/0.50                     ( ?[E:$i]:
% 0.22/0.50                       ( ( ( E ) = ( D ) ) & 
% 0.22/0.50                         ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i]:
% 0.22/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.50            ( l1_pre_topc @ A ) ) =>
% 0.22/0.50          ( ![B:$i]:
% 0.22/0.50            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.22/0.50              ( ![C:$i]:
% 0.22/0.50                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.50                  ( ( m1_pre_topc @ B @ C ) =>
% 0.22/0.50                    ( ![D:$i]:
% 0.22/0.50                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.22/0.50                        ( ?[E:$i]:
% 0.22/0.50                          ( ( ( E ) = ( D ) ) & 
% 0.22/0.50                            ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t15_tmap_1])).
% 0.22/0.50  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('1', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t1_tsep_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l1_pre_topc @ A ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.50           ( m1_subset_1 @
% 0.22/0.50             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (![X19 : $i, X20 : $i]:
% 0.22/0.50         (~ (m1_pre_topc @ X19 @ X20)
% 0.22/0.50          | (m1_subset_1 @ (u1_struct_0 @ X19) @ 
% 0.22/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.22/0.50          | ~ (l1_pre_topc @ X20))),
% 0.22/0.50      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      ((~ (l1_pre_topc @ sk_C)
% 0.22/0.50        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.50           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.50  thf('4', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(dt_m1_pre_topc, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l1_pre_topc @ A ) =>
% 0.22/0.50       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      (![X16 : $i, X17 : $i]:
% 0.22/0.50         (~ (m1_pre_topc @ X16 @ X17)
% 0.22/0.50          | (l1_pre_topc @ X16)
% 0.22/0.50          | ~ (l1_pre_topc @ X17))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.50  thf('6', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.50  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('8', plain, ((l1_pre_topc @ sk_C)),
% 0.22/0.50      inference('demod', [status(thm)], ['6', '7'])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.22/0.50      inference('demod', [status(thm)], ['3', '8'])).
% 0.22/0.50  thf(t3_subset, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      (![X12 : $i, X13 : $i]:
% 0.22/0.50         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.50  thf('11', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.50  thf(t12_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (![X6 : $i, X7 : $i]:
% 0.22/0.50         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.22/0.50      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      (((k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.22/0.50         = (u1_struct_0 @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.50  thf('14', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t2_subset, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ A @ B ) =>
% 0.22/0.50       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      (![X10 : $i, X11 : $i]:
% 0.22/0.50         ((r2_hidden @ X10 @ X11)
% 0.22/0.50          | (v1_xboole_0 @ X11)
% 0.22/0.50          | ~ (m1_subset_1 @ X10 @ X11))),
% 0.22/0.50      inference('cnf', [status(esa)], [t2_subset])).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.50        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.50  thf(d3_xboole_0, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.22/0.50       ( ![D:$i]:
% 0.22/0.50         ( ( r2_hidden @ D @ C ) <=>
% 0.22/0.50           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X0 @ X3)
% 0.22/0.50          | (r2_hidden @ X0 @ X2)
% 0.22/0.50          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.22/0.50         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 0.22/0.50      inference('simplify', [status(thm)], ['17'])).
% 0.22/0.50  thf('19', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.50          | (r2_hidden @ sk_D_1 @ (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['16', '18'])).
% 0.22/0.50  thf(t1_subset, axiom,
% 0.22/0.50    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 0.22/0.50      inference('cnf', [status(esa)], [t1_subset])).
% 0.22/0.50  thf('21', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.50          | (m1_subset_1 @ sk_D_1 @ (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.50  thf('22', plain,
% 0.22/0.50      (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.22/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.50      inference('sup+', [status(thm)], ['13', '21'])).
% 0.22/0.50  thf('23', plain,
% 0.22/0.50      (![X21 : $i]:
% 0.22/0.50         (((X21) != (sk_D_1)) | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ sk_C)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('24', plain, (~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C))),
% 0.22/0.50      inference('simplify', [status(thm)], ['23'])).
% 0.22/0.50  thf('25', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 0.22/0.50      inference('clc', [status(thm)], ['22', '24'])).
% 0.22/0.50  thf(fc2_struct_0, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.50       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.50  thf('26', plain,
% 0.22/0.50      (![X18 : $i]:
% 0.22/0.50         (~ (v1_xboole_0 @ (u1_struct_0 @ X18))
% 0.22/0.50          | ~ (l1_struct_0 @ X18)
% 0.22/0.50          | (v2_struct_0 @ X18))),
% 0.22/0.50      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.22/0.50  thf('27', plain, (((v2_struct_0 @ sk_B) | ~ (l1_struct_0 @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.50  thf('28', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('29', plain,
% 0.22/0.50      (![X16 : $i, X17 : $i]:
% 0.22/0.50         (~ (m1_pre_topc @ X16 @ X17)
% 0.22/0.50          | (l1_pre_topc @ X16)
% 0.22/0.50          | ~ (l1_pre_topc @ X17))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.50  thf('30', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.50  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('32', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.50      inference('demod', [status(thm)], ['30', '31'])).
% 0.22/0.50  thf(dt_l1_pre_topc, axiom,
% 0.22/0.50    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.22/0.50  thf('33', plain,
% 0.22/0.50      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.50  thf('34', plain, ((l1_struct_0 @ sk_B)),
% 0.22/0.50      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.50  thf('35', plain, ((v2_struct_0 @ sk_B)),
% 0.22/0.50      inference('demod', [status(thm)], ['27', '34'])).
% 0.22/0.50  thf('36', plain, ($false), inference('demod', [status(thm)], ['0', '35'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
