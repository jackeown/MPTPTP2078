%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hjJ7o7G6zU

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   62 (  91 expanded)
%              Number of leaves         :   21 (  36 expanded)
%              Depth                    :   15
%              Number of atoms          :  311 ( 967 expanded)
%              Number of equality atoms :    3 (  23 expanded)
%              Maximal formula depth    :   15 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_pre_topc @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( l1_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('13',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( m1_subset_1 @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X12: $i] :
      ( ( X12 != sk_D )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['17','19'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('21',plain,(
    ! [X9: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['9','10'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('24',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('25',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X9: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( l1_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('37',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v2_struct_0 @ sk_B ),
    inference(demod,[status(thm)],['30','37'])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['0','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hjJ7o7G6zU
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:37:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.45  % Solved by: fo/fo7.sh
% 0.21/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.45  % done 47 iterations in 0.013s
% 0.21/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.45  % SZS output start Refutation
% 0.21/0.45  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.45  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.45  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.45  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.45  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.45  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.45  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.45  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.45  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.45  thf(t15_tmap_1, conjecture,
% 0.21/0.45    (![A:$i]:
% 0.21/0.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.45       ( ![B:$i]:
% 0.21/0.45         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.45           ( ![C:$i]:
% 0.21/0.45             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.45               ( ( m1_pre_topc @ B @ C ) =>
% 0.21/0.45                 ( ![D:$i]:
% 0.21/0.45                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.45                     ( ?[E:$i]:
% 0.21/0.45                       ( ( ( E ) = ( D ) ) & 
% 0.21/0.45                         ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.45    (~( ![A:$i]:
% 0.21/0.45        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.45            ( l1_pre_topc @ A ) ) =>
% 0.21/0.45          ( ![B:$i]:
% 0.21/0.45            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.45              ( ![C:$i]:
% 0.21/0.45                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.45                  ( ( m1_pre_topc @ B @ C ) =>
% 0.21/0.45                    ( ![D:$i]:
% 0.21/0.45                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.45                        ( ?[E:$i]:
% 0.21/0.45                          ( ( ( E ) = ( D ) ) & 
% 0.21/0.45                            ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.45    inference('cnf.neg', [status(esa)], [t15_tmap_1])).
% 0.21/0.45  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('1', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf(d2_subset_1, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( ( v1_xboole_0 @ A ) =>
% 0.21/0.45         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.21/0.45       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.45         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.45  thf('2', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i]:
% 0.21/0.45         (~ (m1_subset_1 @ X0 @ X1)
% 0.21/0.45          | (r2_hidden @ X0 @ X1)
% 0.21/0.45          | (v1_xboole_0 @ X1))),
% 0.21/0.45      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.45  thf('3', plain,
% 0.21/0.45      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.45        | (r2_hidden @ sk_D @ (u1_struct_0 @ sk_B)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.45  thf('4', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf(t1_tsep_1, axiom,
% 0.21/0.45    (![A:$i]:
% 0.21/0.45     ( ( l1_pre_topc @ A ) =>
% 0.21/0.45       ( ![B:$i]:
% 0.21/0.45         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.45           ( m1_subset_1 @
% 0.21/0.45             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.45  thf('5', plain,
% 0.21/0.45      (![X10 : $i, X11 : $i]:
% 0.21/0.45         (~ (m1_pre_topc @ X10 @ X11)
% 0.21/0.45          | (m1_subset_1 @ (u1_struct_0 @ X10) @ 
% 0.21/0.45             (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.45          | ~ (l1_pre_topc @ X11))),
% 0.21/0.45      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.21/0.45  thf('6', plain,
% 0.21/0.45      ((~ (l1_pre_topc @ sk_C)
% 0.21/0.45        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.45           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C))))),
% 0.21/0.45      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.45  thf('7', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf(dt_m1_pre_topc, axiom,
% 0.21/0.45    (![A:$i]:
% 0.21/0.45     ( ( l1_pre_topc @ A ) =>
% 0.21/0.45       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.45  thf('8', plain,
% 0.21/0.45      (![X7 : $i, X8 : $i]:
% 0.21/0.45         (~ (m1_pre_topc @ X7 @ X8) | (l1_pre_topc @ X7) | ~ (l1_pre_topc @ X8))),
% 0.21/0.45      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.45  thf('9', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.21/0.45      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.45  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('11', plain, ((l1_pre_topc @ sk_C)),
% 0.21/0.45      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.45  thf('12', plain,
% 0.21/0.45      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.45        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.21/0.45      inference('demod', [status(thm)], ['6', '11'])).
% 0.21/0.45  thf(l3_subset_1, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.45       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.21/0.45  thf('13', plain,
% 0.21/0.45      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.45         (~ (r2_hidden @ X3 @ X4)
% 0.21/0.45          | (r2_hidden @ X3 @ X5)
% 0.21/0.45          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.21/0.45      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.21/0.45  thf('14', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_C))
% 0.21/0.45          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.45  thf('15', plain,
% 0.21/0.45      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.45        | (r2_hidden @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['3', '14'])).
% 0.21/0.45  thf('16', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i]:
% 0.21/0.45         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.45          | (m1_subset_1 @ X0 @ X1)
% 0.21/0.45          | (v1_xboole_0 @ X1))),
% 0.21/0.45      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.45  thf('17', plain,
% 0.21/0.45      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.45        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.21/0.45        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.45  thf('18', plain,
% 0.21/0.45      (![X12 : $i]:
% 0.21/0.45         (((X12) != (sk_D)) | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ sk_C)))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('19', plain, (~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))),
% 0.21/0.45      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.45  thf('20', plain,
% 0.21/0.45      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.21/0.45        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.45      inference('clc', [status(thm)], ['17', '19'])).
% 0.21/0.45  thf(fc2_struct_0, axiom,
% 0.21/0.45    (![A:$i]:
% 0.21/0.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.45       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.45  thf('21', plain,
% 0.21/0.45      (![X9 : $i]:
% 0.21/0.45         (~ (v1_xboole_0 @ (u1_struct_0 @ X9))
% 0.21/0.45          | ~ (l1_struct_0 @ X9)
% 0.21/0.45          | (v2_struct_0 @ X9))),
% 0.21/0.45      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.45  thf('22', plain,
% 0.21/0.45      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.45        | (v2_struct_0 @ sk_C)
% 0.21/0.45        | ~ (l1_struct_0 @ sk_C))),
% 0.21/0.45      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.45  thf('23', plain, ((l1_pre_topc @ sk_C)),
% 0.21/0.45      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.45  thf(dt_l1_pre_topc, axiom,
% 0.21/0.45    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.45  thf('24', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.21/0.45      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.45  thf('25', plain, ((l1_struct_0 @ sk_C)),
% 0.21/0.45      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.45  thf('26', plain,
% 0.21/0.45      (((v1_xboole_0 @ (u1_struct_0 @ sk_B)) | (v2_struct_0 @ sk_C))),
% 0.21/0.45      inference('demod', [status(thm)], ['22', '25'])).
% 0.21/0.45  thf('27', plain, (~ (v2_struct_0 @ sk_C)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('28', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 0.21/0.45      inference('clc', [status(thm)], ['26', '27'])).
% 0.21/0.45  thf('29', plain,
% 0.21/0.45      (![X9 : $i]:
% 0.21/0.45         (~ (v1_xboole_0 @ (u1_struct_0 @ X9))
% 0.21/0.45          | ~ (l1_struct_0 @ X9)
% 0.21/0.45          | (v2_struct_0 @ X9))),
% 0.21/0.45      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.45  thf('30', plain, (((v2_struct_0 @ sk_B) | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.45      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.45  thf('31', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('32', plain,
% 0.21/0.45      (![X7 : $i, X8 : $i]:
% 0.21/0.45         (~ (m1_pre_topc @ X7 @ X8) | (l1_pre_topc @ X7) | ~ (l1_pre_topc @ X8))),
% 0.21/0.45      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.45  thf('33', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.21/0.45      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.45  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('35', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.45      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.45  thf('36', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.21/0.45      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.45  thf('37', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.45      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.45  thf('38', plain, ((v2_struct_0 @ sk_B)),
% 0.21/0.45      inference('demod', [status(thm)], ['30', '37'])).
% 0.21/0.45  thf('39', plain, ($false), inference('demod', [status(thm)], ['0', '38'])).
% 0.21/0.45  
% 0.21/0.45  % SZS output end Refutation
% 0.21/0.45  
% 0.21/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
