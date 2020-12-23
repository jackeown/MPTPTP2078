%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CNjbzbqxkh

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:00 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 100 expanded)
%              Number of leaves         :   22 (  40 expanded)
%              Depth                    :   15
%              Number of atoms          :  485 ( 920 expanded)
%              Number of equality atoms :   46 (  73 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(d2_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_tdlat_3 @ A )
      <=> ( ( u1_pre_topc @ A )
          = ( k2_tarski @ k1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X13: $i] :
      ( ~ ( v2_tdlat_3 @ X13 )
      | ( ( u1_pre_topc @ X13 )
        = ( k2_tarski @ k1_xboole_0 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_tdlat_3])).

thf('1',plain,(
    ! [X13: $i] :
      ( ~ ( v2_tdlat_3 @ X13 )
      | ( ( u1_pre_topc @ X13 )
        = ( k2_tarski @ k1_xboole_0 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_tdlat_3])).

thf(t18_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
              & ( v2_tdlat_3 @ A ) )
           => ( v2_tdlat_3 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( l1_pre_topc @ B )
           => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                  = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                & ( v2_tdlat_3 @ A ) )
             => ( v2_tdlat_3 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_tex_2])).

thf('2',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('3',plain,(
    ! [X2: $i] :
      ( r1_tarski @ k1_xboole_0 @ X2 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X3 @ X4 ) )
      = ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf(t100_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ) )).

thf('7',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ ( k1_zfmisc_1 @ ( k3_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_tarski @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_tarski @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( ( g1_pre_topc @ X11 @ X12 )
       != ( g1_pre_topc @ X9 @ X10 ) )
      | ( X11 = X9 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( ( g1_pre_topc @ X0 @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
       != ( g1_pre_topc @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( g1_pre_topc @ X0 @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( X0
        = ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_tdlat_3 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['1','14'])).

thf('16',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['15'])).

thf('17',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ! [X13: $i] :
      ( ( ( u1_pre_topc @ X13 )
       != ( k2_tarski @ k1_xboole_0 @ ( u1_struct_0 @ X13 ) ) )
      | ( v2_tdlat_3 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_tdlat_3])).

thf('21',plain,
    ( ( ( u1_pre_topc @ sk_B )
     != ( k2_tarski @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_tdlat_3 @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X13: $i] :
      ( ~ ( v2_tdlat_3 @ X13 )
      | ( ( u1_pre_topc @ X13 )
        = ( k2_tarski @ k1_xboole_0 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_tdlat_3])).

thf('24',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X3 @ X4 ) )
      = ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ ( u1_pre_topc @ X0 ) )
        = ( k2_xboole_0 @ k1_xboole_0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_tdlat_3 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ ( u1_pre_topc @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_tdlat_3 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ ( k1_zfmisc_1 @ ( k3_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_zfmisc_1])).

thf('29',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k3_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( ( g1_pre_topc @ X11 @ X12 )
       != ( g1_pre_topc @ X9 @ X10 ) )
      | ( X12 = X10 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( ( g1_pre_topc @ ( k3_tarski @ X0 ) @ X0 )
       != ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( v2_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( ( u1_pre_topc @ X0 )
        = ( u1_pre_topc @ sk_B ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_tdlat_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','33'])).

thf('35',plain,
    ( ~ ( v2_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( u1_pre_topc @ sk_B ) ) ),
    inference(eq_res,[status(thm)],['34'])).

thf('36',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( u1_pre_topc @ sk_A )
    = ( u1_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( k2_tarski @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_tdlat_3 @ sk_B ) ),
    inference(demod,[status(thm)],['21','38','39'])).

thf('41',plain,(
    ~ ( v2_tdlat_3 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ( u1_pre_topc @ sk_A )
 != ( k2_tarski @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( u1_pre_topc @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ( u1_pre_topc @ sk_A )
 != ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    $false ),
    inference(simplify,[status(thm)],['46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CNjbzbqxkh
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:09:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 80 iterations in 0.036s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.22/0.50  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.22/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(d2_tdlat_3, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l1_pre_topc @ A ) =>
% 0.22/0.50       ( ( v2_tdlat_3 @ A ) <=>
% 0.22/0.50         ( ( u1_pre_topc @ A ) =
% 0.22/0.50           ( k2_tarski @ k1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      (![X13 : $i]:
% 0.22/0.50         (~ (v2_tdlat_3 @ X13)
% 0.22/0.50          | ((u1_pre_topc @ X13)
% 0.22/0.50              = (k2_tarski @ k1_xboole_0 @ (u1_struct_0 @ X13)))
% 0.22/0.50          | ~ (l1_pre_topc @ X13))),
% 0.22/0.50      inference('cnf', [status(esa)], [d2_tdlat_3])).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      (![X13 : $i]:
% 0.22/0.50         (~ (v2_tdlat_3 @ X13)
% 0.22/0.50          | ((u1_pre_topc @ X13)
% 0.22/0.50              = (k2_tarski @ k1_xboole_0 @ (u1_struct_0 @ X13)))
% 0.22/0.50          | ~ (l1_pre_topc @ X13))),
% 0.22/0.50      inference('cnf', [status(esa)], [d2_tdlat_3])).
% 0.22/0.50  thf(t18_tex_2, conjecture,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l1_pre_topc @ A ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( l1_pre_topc @ B ) =>
% 0.22/0.50           ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.22/0.50                 ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.22/0.50               ( v2_tdlat_3 @ A ) ) =>
% 0.22/0.50             ( v2_tdlat_3 @ B ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i]:
% 0.22/0.50        ( ( l1_pre_topc @ A ) =>
% 0.22/0.50          ( ![B:$i]:
% 0.22/0.50            ( ( l1_pre_topc @ B ) =>
% 0.22/0.50              ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.22/0.50                    ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.22/0.50                  ( v2_tdlat_3 @ A ) ) =>
% 0.22/0.50                ( v2_tdlat_3 @ B ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t18_tex_2])).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.50         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.50  thf('3', plain, (![X2 : $i]: (r1_tarski @ k1_xboole_0 @ X2)),
% 0.22/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.50  thf(t12_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.22/0.50  thf('5', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.50  thf(l51_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (![X3 : $i, X4 : $i]:
% 0.22/0.50         ((k3_tarski @ (k2_tarski @ X3 @ X4)) = (k2_xboole_0 @ X3 @ X4))),
% 0.22/0.50      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.22/0.50  thf(t100_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i]: ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ))).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (![X5 : $i]: (r1_tarski @ X5 @ (k1_zfmisc_1 @ (k3_tarski @ X5)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t100_zfmisc_1])).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (r1_tarski @ (k2_tarski @ X1 @ X0) @ 
% 0.22/0.50          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.22/0.50      inference('sup+', [status(thm)], ['6', '7'])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (r1_tarski @ (k2_tarski @ k1_xboole_0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.22/0.50      inference('sup+', [status(thm)], ['5', '8'])).
% 0.22/0.50  thf(t3_subset, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      (![X6 : $i, X8 : $i]:
% 0.22/0.50         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.22/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (m1_subset_1 @ (k2_tarski @ k1_xboole_0 @ X0) @ 
% 0.22/0.50          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.50  thf(free_g1_pre_topc, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.50       ( ![C:$i,D:$i]:
% 0.22/0.50         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.22/0.50           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.50         (((g1_pre_topc @ X11 @ X12) != (g1_pre_topc @ X9 @ X10))
% 0.22/0.50          | ((X11) = (X9))
% 0.22/0.50          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11))))),
% 0.22/0.50      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         (((X0) = (X1))
% 0.22/0.50          | ((g1_pre_topc @ X0 @ (k2_tarski @ k1_xboole_0 @ X0))
% 0.22/0.50              != (g1_pre_topc @ X1 @ X2)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((g1_pre_topc @ X0 @ (k2_tarski @ k1_xboole_0 @ X0))
% 0.22/0.50            != (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.22/0.50          | ((X0) = (u1_struct_0 @ sk_B)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['2', '13'])).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.22/0.50            != (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.22/0.50          | ~ (l1_pre_topc @ X0)
% 0.22/0.50          | ~ (v2_tdlat_3 @ X0)
% 0.22/0.50          | ((u1_struct_0 @ X0) = (u1_struct_0 @ sk_B)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['1', '14'])).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      ((((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))
% 0.22/0.50        | ~ (v2_tdlat_3 @ sk_A)
% 0.22/0.50        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.50      inference('eq_res', [status(thm)], ['15'])).
% 0.22/0.50  thf('17', plain, ((v2_tdlat_3 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('19', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      (![X13 : $i]:
% 0.22/0.50         (((u1_pre_topc @ X13)
% 0.22/0.50            != (k2_tarski @ k1_xboole_0 @ (u1_struct_0 @ X13)))
% 0.22/0.50          | (v2_tdlat_3 @ X13)
% 0.22/0.50          | ~ (l1_pre_topc @ X13))),
% 0.22/0.50      inference('cnf', [status(esa)], [d2_tdlat_3])).
% 0.22/0.50  thf('21', plain,
% 0.22/0.50      ((((u1_pre_topc @ sk_B)
% 0.22/0.50          != (k2_tarski @ k1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.22/0.50        | ~ (l1_pre_topc @ sk_B)
% 0.22/0.50        | (v2_tdlat_3 @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.50  thf('22', plain,
% 0.22/0.50      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.50         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('23', plain,
% 0.22/0.50      (![X13 : $i]:
% 0.22/0.50         (~ (v2_tdlat_3 @ X13)
% 0.22/0.50          | ((u1_pre_topc @ X13)
% 0.22/0.50              = (k2_tarski @ k1_xboole_0 @ (u1_struct_0 @ X13)))
% 0.22/0.50          | ~ (l1_pre_topc @ X13))),
% 0.22/0.50      inference('cnf', [status(esa)], [d2_tdlat_3])).
% 0.22/0.50  thf('24', plain,
% 0.22/0.50      (![X3 : $i, X4 : $i]:
% 0.22/0.50         ((k3_tarski @ (k2_tarski @ X3 @ X4)) = (k2_xboole_0 @ X3 @ X4))),
% 0.22/0.50      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.22/0.50  thf('25', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((k3_tarski @ (u1_pre_topc @ X0))
% 0.22/0.50            = (k2_xboole_0 @ k1_xboole_0 @ (u1_struct_0 @ X0)))
% 0.22/0.50          | ~ (l1_pre_topc @ X0)
% 0.22/0.50          | ~ (v2_tdlat_3 @ X0))),
% 0.22/0.50      inference('sup+', [status(thm)], ['23', '24'])).
% 0.22/0.50  thf('26', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((k3_tarski @ (u1_pre_topc @ X0)) = (u1_struct_0 @ X0))
% 0.22/0.50          | ~ (l1_pre_topc @ X0)
% 0.22/0.50          | ~ (v2_tdlat_3 @ X0))),
% 0.22/0.50      inference('demod', [status(thm)], ['25', '26'])).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      (![X5 : $i]: (r1_tarski @ X5 @ (k1_zfmisc_1 @ (k3_tarski @ X5)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t100_zfmisc_1])).
% 0.22/0.50  thf('29', plain,
% 0.22/0.50      (![X6 : $i, X8 : $i]:
% 0.22/0.50         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.22/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.50  thf('30', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k3_tarski @ X0))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.50  thf('31', plain,
% 0.22/0.50      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.50         (((g1_pre_topc @ X11 @ X12) != (g1_pre_topc @ X9 @ X10))
% 0.22/0.50          | ((X12) = (X10))
% 0.22/0.50          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11))))),
% 0.22/0.50      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.22/0.50  thf('32', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         (((X0) = (X1))
% 0.22/0.50          | ((g1_pre_topc @ (k3_tarski @ X0) @ X0) != (g1_pre_topc @ X2 @ X1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.50  thf('33', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         (((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.22/0.50            != (g1_pre_topc @ X2 @ X1))
% 0.22/0.50          | ~ (v2_tdlat_3 @ X0)
% 0.22/0.50          | ~ (l1_pre_topc @ X0)
% 0.22/0.50          | ((u1_pre_topc @ X0) = (X1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['27', '32'])).
% 0.22/0.50  thf('34', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.22/0.50            != (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.22/0.50          | ((u1_pre_topc @ X0) = (u1_pre_topc @ sk_B))
% 0.22/0.50          | ~ (l1_pre_topc @ X0)
% 0.22/0.50          | ~ (v2_tdlat_3 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['22', '33'])).
% 0.22/0.50  thf('35', plain,
% 0.22/0.50      ((~ (v2_tdlat_3 @ sk_A)
% 0.22/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.50        | ((u1_pre_topc @ sk_A) = (u1_pre_topc @ sk_B)))),
% 0.22/0.50      inference('eq_res', [status(thm)], ['34'])).
% 0.22/0.50  thf('36', plain, ((v2_tdlat_3 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('38', plain, (((u1_pre_topc @ sk_A) = (u1_pre_topc @ sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.22/0.50  thf('39', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('40', plain,
% 0.22/0.50      ((((u1_pre_topc @ sk_A)
% 0.22/0.50          != (k2_tarski @ k1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.22/0.50        | (v2_tdlat_3 @ sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['21', '38', '39'])).
% 0.22/0.50  thf('41', plain, (~ (v2_tdlat_3 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('42', plain,
% 0.22/0.50      (((u1_pre_topc @ sk_A)
% 0.22/0.50         != (k2_tarski @ k1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.50      inference('clc', [status(thm)], ['40', '41'])).
% 0.22/0.50  thf('43', plain,
% 0.22/0.50      ((((u1_pre_topc @ sk_A) != (u1_pre_topc @ sk_A))
% 0.22/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.50        | ~ (v2_tdlat_3 @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['0', '42'])).
% 0.22/0.50  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('45', plain, ((v2_tdlat_3 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('46', plain, (((u1_pre_topc @ sk_A) != (u1_pre_topc @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.22/0.50  thf('47', plain, ($false), inference('simplify', [status(thm)], ['46'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
