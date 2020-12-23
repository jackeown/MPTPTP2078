%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7RgTotguFL

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 176 expanded)
%              Number of leaves         :   22 (  64 expanded)
%              Depth                    :   22
%              Number of atoms          :  524 (1659 expanded)
%              Number of equality atoms :   55 ( 152 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(d2_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_tdlat_3 @ A )
      <=> ( ( u1_pre_topc @ A )
          = ( k2_tarski @ k1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X18: $i] :
      ( ~ ( v2_tdlat_3 @ X18 )
      | ( ( u1_pre_topc @ X18 )
        = ( k2_tarski @ k1_xboole_0 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d2_tdlat_3])).

thf('1',plain,(
    ! [X18: $i] :
      ( ~ ( v2_tdlat_3 @ X18 )
      | ( ( u1_pre_topc @ X18 )
        = ( k2_tarski @ k1_xboole_0 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d2_tdlat_3])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X8 @ X9 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ ( u1_pre_topc @ X0 ) )
        = ( k2_xboole_0 @ k1_xboole_0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_tdlat_3 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('4',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k2_tarski @ X2 @ X1 )
      = ( k2_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X8 @ X9 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X8 @ X9 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ ( u1_pre_topc @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_tdlat_3 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ ( u1_pre_topc @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_tdlat_3 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','10'])).

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

thf('13',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ ( u1_pre_topc @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_tdlat_3 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','10'])).

thf(t100_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ) )).

thf('16',plain,(
    ! [X10: $i] :
      ( r1_tarski @ X10 @ ( k1_zfmisc_1 @ ( k3_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_zfmisc_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k3_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('19',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( ( g1_pre_topc @ X16 @ X17 )
       != ( g1_pre_topc @ X14 @ X15 ) )
      | ( X17 = X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( ( g1_pre_topc @ ( k3_tarski @ X0 ) @ X0 )
       != ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( v2_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( ( u1_pre_topc @ X0 )
        = ( u1_pre_topc @ sk_B ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_tdlat_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,
    ( ~ ( v2_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( u1_pre_topc @ sk_B ) ) ),
    inference(eq_res,[status(thm)],['22'])).

thf('24',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( u1_pre_topc @ sk_A )
    = ( u1_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k3_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('29',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( ( g1_pre_topc @ X16 @ X17 )
       != ( g1_pre_topc @ X14 @ X15 ) )
      | ( X16 = X14 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_tarski @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( k3_tarski @ X0 ) @ X0 )
       != ( g1_pre_topc @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( g1_pre_topc @ ( k3_tarski @ X0 ) @ X0 )
       != ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( ( k3_tarski @ X0 )
        = ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v2_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k3_tarski @ ( u1_pre_topc @ X0 ) )
        = ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['12','31'])).

thf('33',plain,
    ( ( ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
      = ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_tdlat_3 @ sk_A ) ),
    inference(eq_res,[status(thm)],['32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['11','36'])).

thf('38',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X18: $i] :
      ( ( ( u1_pre_topc @ X18 )
       != ( k2_tarski @ k1_xboole_0 @ ( u1_struct_0 @ X18 ) ) )
      | ( v2_tdlat_3 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d2_tdlat_3])).

thf('42',plain,
    ( ( ( u1_pre_topc @ sk_B )
     != ( k2_tarski @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_tdlat_3 @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( u1_pre_topc @ sk_A )
    = ( u1_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('44',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( k2_tarski @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_tdlat_3 @ sk_B ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ~ ( v2_tdlat_3 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ( u1_pre_topc @ sk_A )
 != ( k2_tarski @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( u1_pre_topc @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ( u1_pre_topc @ sk_A )
 != ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    $false ),
    inference(simplify,[status(thm)],['51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7RgTotguFL
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:40:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 69 iterations in 0.037s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.21/0.51  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.51  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.51  thf(d2_tdlat_3, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ( v2_tdlat_3 @ A ) <=>
% 0.21/0.51         ( ( u1_pre_topc @ A ) =
% 0.21/0.51           ( k2_tarski @ k1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      (![X18 : $i]:
% 0.21/0.51         (~ (v2_tdlat_3 @ X18)
% 0.21/0.51          | ((u1_pre_topc @ X18)
% 0.21/0.51              = (k2_tarski @ k1_xboole_0 @ (u1_struct_0 @ X18)))
% 0.21/0.51          | ~ (l1_pre_topc @ X18))),
% 0.21/0.51      inference('cnf', [status(esa)], [d2_tdlat_3])).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (![X18 : $i]:
% 0.21/0.51         (~ (v2_tdlat_3 @ X18)
% 0.21/0.51          | ((u1_pre_topc @ X18)
% 0.21/0.51              = (k2_tarski @ k1_xboole_0 @ (u1_struct_0 @ X18)))
% 0.21/0.51          | ~ (l1_pre_topc @ X18))),
% 0.21/0.51      inference('cnf', [status(esa)], [d2_tdlat_3])).
% 0.21/0.51  thf(l51_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X8 : $i, X9 : $i]:
% 0.21/0.51         ((k3_tarski @ (k2_tarski @ X8 @ X9)) = (k2_xboole_0 @ X8 @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((k3_tarski @ (u1_pre_topc @ X0))
% 0.21/0.51            = (k2_xboole_0 @ k1_xboole_0 @ (u1_struct_0 @ X0)))
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | ~ (v2_tdlat_3 @ X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.51  thf(commutativity_k2_tarski, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X1 : $i, X2 : $i]: ((k2_tarski @ X2 @ X1) = (k2_tarski @ X1 @ X2))),
% 0.21/0.51      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X8 : $i, X9 : $i]:
% 0.21/0.51         ((k3_tarski @ (k2_tarski @ X8 @ X9)) = (k2_xboole_0 @ X8 @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('sup+', [status(thm)], ['4', '5'])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X8 : $i, X9 : $i]:
% 0.21/0.51         ((k3_tarski @ (k2_tarski @ X8 @ X9)) = (k2_xboole_0 @ X8 @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.51  thf(t1_boole, axiom,
% 0.21/0.51    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.51  thf('9', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.51      inference('cnf', [status(esa)], [t1_boole])).
% 0.21/0.51  thf('10', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((k3_tarski @ (u1_pre_topc @ X0)) = (u1_struct_0 @ X0))
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | ~ (v2_tdlat_3 @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['3', '10'])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((k3_tarski @ (u1_pre_topc @ X0)) = (u1_struct_0 @ X0))
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | ~ (v2_tdlat_3 @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['3', '10'])).
% 0.21/0.51  thf(t18_tex_2, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( l1_pre_topc @ B ) =>
% 0.21/0.51           ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.21/0.51                 ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.21/0.51               ( v2_tdlat_3 @ A ) ) =>
% 0.21/0.51             ( v2_tdlat_3 @ B ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( l1_pre_topc @ A ) =>
% 0.21/0.51          ( ![B:$i]:
% 0.21/0.51            ( ( l1_pre_topc @ B ) =>
% 0.21/0.51              ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.21/0.51                    ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.21/0.51                  ( v2_tdlat_3 @ A ) ) =>
% 0.21/0.51                ( v2_tdlat_3 @ B ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t18_tex_2])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.51         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.51         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((k3_tarski @ (u1_pre_topc @ X0)) = (u1_struct_0 @ X0))
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | ~ (v2_tdlat_3 @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['3', '10'])).
% 0.21/0.51  thf(t100_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i]: ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ))).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X10 : $i]: (r1_tarski @ X10 @ (k1_zfmisc_1 @ (k3_tarski @ X10)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t100_zfmisc_1])).
% 0.21/0.51  thf(t3_subset, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (![X11 : $i, X13 : $i]:
% 0.21/0.51         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.21/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k3_tarski @ X0))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.51  thf(free_g1_pre_topc, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.51       ( ![C:$i,D:$i]:
% 0.21/0.51         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.21/0.51           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.51         (((g1_pre_topc @ X16 @ X17) != (g1_pre_topc @ X14 @ X15))
% 0.21/0.51          | ((X17) = (X15))
% 0.21/0.51          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 0.21/0.51      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (((X0) = (X1))
% 0.21/0.51          | ((g1_pre_topc @ (k3_tarski @ X0) @ X0) != (g1_pre_topc @ X2 @ X1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.21/0.51            != (g1_pre_topc @ X2 @ X1))
% 0.21/0.51          | ~ (v2_tdlat_3 @ X0)
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | ((u1_pre_topc @ X0) = (X1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['15', '20'])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.21/0.51            != (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.51          | ((u1_pre_topc @ X0) = (u1_pre_topc @ sk_B))
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | ~ (v2_tdlat_3 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['14', '21'])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      ((~ (v2_tdlat_3 @ sk_A)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | ((u1_pre_topc @ sk_A) = (u1_pre_topc @ sk_B)))),
% 0.21/0.51      inference('eq_res', [status(thm)], ['22'])).
% 0.21/0.51  thf('24', plain, ((v2_tdlat_3 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('26', plain, (((u1_pre_topc @ sk_A) = (u1_pre_topc @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.51         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['13', '26'])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k3_tarski @ X0))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.51         (((g1_pre_topc @ X16 @ X17) != (g1_pre_topc @ X14 @ X15))
% 0.21/0.51          | ((X16) = (X14))
% 0.21/0.51          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 0.21/0.51      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (((k3_tarski @ X0) = (X1))
% 0.21/0.51          | ((g1_pre_topc @ (k3_tarski @ X0) @ X0) != (g1_pre_topc @ X1 @ X2)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((g1_pre_topc @ (k3_tarski @ X0) @ X0)
% 0.21/0.51            != (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.51          | ((k3_tarski @ X0) = (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['27', '30'])).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.21/0.51            != (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.51          | ~ (v2_tdlat_3 @ X0)
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | ((k3_tarski @ (u1_pre_topc @ X0)) = (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['12', '31'])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      ((((k3_tarski @ (u1_pre_topc @ sk_A)) = (u1_struct_0 @ sk_B))
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | ~ (v2_tdlat_3 @ sk_A))),
% 0.21/0.51      inference('eq_res', [status(thm)], ['32'])).
% 0.21/0.51  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('35', plain, ((v2_tdlat_3 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      (((k3_tarski @ (u1_pre_topc @ sk_A)) = (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      ((((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))
% 0.21/0.51        | ~ (v2_tdlat_3 @ sk_A)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.51      inference('sup+', [status(thm)], ['11', '36'])).
% 0.21/0.51  thf('38', plain, ((v2_tdlat_3 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('40', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.21/0.51  thf('41', plain,
% 0.21/0.51      (![X18 : $i]:
% 0.21/0.51         (((u1_pre_topc @ X18)
% 0.21/0.51            != (k2_tarski @ k1_xboole_0 @ (u1_struct_0 @ X18)))
% 0.21/0.51          | (v2_tdlat_3 @ X18)
% 0.21/0.51          | ~ (l1_pre_topc @ X18))),
% 0.21/0.51      inference('cnf', [status(esa)], [d2_tdlat_3])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      ((((u1_pre_topc @ sk_B)
% 0.21/0.51          != (k2_tarski @ k1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51        | ~ (l1_pre_topc @ sk_B)
% 0.21/0.51        | (v2_tdlat_3 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.51  thf('43', plain, (((u1_pre_topc @ sk_A) = (u1_pre_topc @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.21/0.51  thf('44', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      ((((u1_pre_topc @ sk_A)
% 0.21/0.51          != (k2_tarski @ k1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51        | (v2_tdlat_3 @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.21/0.51  thf('46', plain, (~ (v2_tdlat_3 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      (((u1_pre_topc @ sk_A)
% 0.21/0.51         != (k2_tarski @ k1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('clc', [status(thm)], ['45', '46'])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      ((((u1_pre_topc @ sk_A) != (u1_pre_topc @ sk_A))
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | ~ (v2_tdlat_3 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['0', '47'])).
% 0.21/0.51  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('50', plain, ((v2_tdlat_3 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('51', plain, (((u1_pre_topc @ sk_A) != (u1_pre_topc @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.21/0.51  thf('52', plain, ($false), inference('simplify', [status(thm)], ['51'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
