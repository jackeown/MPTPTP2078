%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oqXNSuRFCZ

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 106 expanded)
%              Number of leaves         :   32 (  45 expanded)
%              Depth                    :   16
%              Number of atoms          :  519 ( 676 expanded)
%              Number of equality atoms :   35 (  52 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v4_pre_topc @ X12 @ X13 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('5',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('8',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t31_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v4_pre_topc @ B @ A )
                  & ( r1_tarski @ C @ B ) )
               => ( r1_tarski @ ( k2_pre_topc @ A @ C ) @ B ) ) ) ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v4_pre_topc @ X18 @ X19 )
      | ~ ( r1_tarski @ X20 @ X18 )
      | ( r1_tarski @ ( k2_pre_topc @ X19 @ X20 ) @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t31_tops_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ X0 @ X1 ) @ k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ k1_xboole_0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 )
      | ( r1_tarski @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('18',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X4 ) @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('19',plain,(
    ! [X3: $i] :
      ( ( k2_subset_1 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('20',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( ( k1_tops_1 @ X17 @ X16 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X17 ) @ ( k2_pre_topc @ X17 @ ( k3_subset_1 @ ( u1_struct_0 @ X17 ) @ X16 ) ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('24',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X6 @ ( k3_subset_1 @ X6 @ X5 ) )
        = X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('26',plain,(
    ! [X2: $i] :
      ( ( k1_subset_1 @ X2 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('27',plain,(
    ! [X7: $i] :
      ( ( k2_subset_1 @ X7 )
      = ( k3_subset_1 @ X7 @ ( k1_subset_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf('28',plain,(
    ! [X3: $i] :
      ( ( k2_subset_1 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('29',plain,(
    ! [X7: $i] :
      ( X7
      = ( k3_subset_1 @ X7 @ ( k1_subset_1 @ X7 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['22','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k1_tops_1 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','36'])).

thf(t43_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) )
        = ( k2_struct_0 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) )
          = ( k2_struct_0 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_tops_1])).

thf('38',plain,(
    ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( ( u1_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('43',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('44',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ( u1_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','41','44'])).

thf('46',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','45'])).

thf('47',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['42','43'])).

thf('48',plain,(
    ( k2_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    $false ),
    inference(simplify,[status(thm)],['48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oqXNSuRFCZ
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:19:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 95 iterations in 0.036s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.49  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.49  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.49  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.49  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.20/0.49  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.49  thf(d3_struct_0, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      (![X14 : $i]:
% 0.20/0.49         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X14 : $i]:
% 0.20/0.49         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.49  thf(t4_subset_1, axiom,
% 0.20/0.49    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.20/0.49      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.49  thf(cc2_pre_topc, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X12 : $i, X13 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.49          | (v4_pre_topc @ X12 @ X13)
% 0.20/0.49          | ~ (v1_xboole_0 @ X12)
% 0.20/0.49          | ~ (l1_pre_topc @ X13)
% 0.20/0.49          | ~ (v2_pre_topc @ X13))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v2_pre_topc @ X0)
% 0.20/0.49          | ~ (l1_pre_topc @ X0)
% 0.20/0.49          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.49          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.49  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.49  thf('5', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.49      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v2_pre_topc @ X0)
% 0.20/0.49          | ~ (l1_pre_topc @ X0)
% 0.20/0.49          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.20/0.49      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.20/0.49      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.49  thf(t31_tops_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( l1_pre_topc @ A ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49               ( ( ( v4_pre_topc @ B @ A ) & ( r1_tarski @ C @ B ) ) =>
% 0.20/0.49                 ( r1_tarski @ ( k2_pre_topc @ A @ C ) @ B ) ) ) ) ) ) ))).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.20/0.49          | ~ (v4_pre_topc @ X18 @ X19)
% 0.20/0.49          | ~ (r1_tarski @ X20 @ X18)
% 0.20/0.49          | (r1_tarski @ (k2_pre_topc @ X19 @ X20) @ X18)
% 0.20/0.49          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.20/0.49          | ~ (l1_pre_topc @ X19))),
% 0.20/0.49      inference('cnf', [status(esa)], [t31_tops_1])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (l1_pre_topc @ X0)
% 0.20/0.49          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.49          | (r1_tarski @ (k2_pre_topc @ X0 @ X1) @ k1_xboole_0)
% 0.20/0.49          | ~ (r1_tarski @ X1 @ k1_xboole_0)
% 0.20/0.49          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v4_pre_topc @ k1_xboole_0 @ X0)
% 0.20/0.49          | ~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0)
% 0.20/0.49          | (r1_tarski @ (k2_pre_topc @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.20/0.49          | ~ (l1_pre_topc @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['7', '10'])).
% 0.20/0.49  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.49  thf('12', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.49      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v4_pre_topc @ k1_xboole_0 @ X0)
% 0.20/0.49          | (r1_tarski @ (k2_pre_topc @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.20/0.49          | ~ (l1_pre_topc @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (l1_pre_topc @ X0)
% 0.20/0.49          | ~ (v2_pre_topc @ X0)
% 0.20/0.49          | ~ (l1_pre_topc @ X0)
% 0.20/0.49          | (r1_tarski @ (k2_pre_topc @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['6', '13'])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r1_tarski @ (k2_pre_topc @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.20/0.49          | ~ (v2_pre_topc @ X0)
% 0.20/0.49          | ~ (l1_pre_topc @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.49  thf(t3_xboole_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (r1_tarski @ X1 @ k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (l1_pre_topc @ X0)
% 0.20/0.49          | ~ (v2_pre_topc @ X0)
% 0.20/0.49          | ((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.49  thf(dt_k2_subset_1, axiom,
% 0.20/0.49    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X4 : $i]: (m1_subset_1 @ (k2_subset_1 @ X4) @ (k1_zfmisc_1 @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.20/0.49  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.49  thf('19', plain, (![X3 : $i]: ((k2_subset_1 @ X3) = (X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.49  thf('20', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.20/0.49      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.49  thf(d1_tops_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( l1_pre_topc @ A ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49           ( ( k1_tops_1 @ A @ B ) =
% 0.20/0.49             ( k3_subset_1 @
% 0.20/0.49               ( u1_struct_0 @ A ) @ 
% 0.20/0.49               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (![X16 : $i, X17 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.49          | ((k1_tops_1 @ X17 @ X16)
% 0.20/0.49              = (k3_subset_1 @ (u1_struct_0 @ X17) @ 
% 0.20/0.49                 (k2_pre_topc @ X17 @ (k3_subset_1 @ (u1_struct_0 @ X17) @ X16))))
% 0.20/0.49          | ~ (l1_pre_topc @ X17))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (l1_pre_topc @ X0)
% 0.20/0.49          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0))
% 0.20/0.49              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.20/0.49                 (k2_pre_topc @ X0 @ 
% 0.20/0.49                  (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0))))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.20/0.49      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.49  thf(involutiveness_k3_subset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.49       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i]:
% 0.20/0.49         (((k3_subset_1 @ X6 @ (k3_subset_1 @ X6 @ X5)) = (X5))
% 0.20/0.49          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.20/0.49      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.49  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.49  thf('26', plain, (![X2 : $i]: ((k1_subset_1 @ X2) = (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.20/0.49  thf(t22_subset_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (![X7 : $i]:
% 0.20/0.49         ((k2_subset_1 @ X7) = (k3_subset_1 @ X7 @ (k1_subset_1 @ X7)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.20/0.49  thf('28', plain, (![X3 : $i]: ((k2_subset_1 @ X3) = (X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (![X7 : $i]: ((X7) = (k3_subset_1 @ X7 @ (k1_subset_1 @ X7)))),
% 0.20/0.49      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.49  thf('30', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['26', '29'])).
% 0.20/0.49  thf('31', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['25', '30'])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (l1_pre_topc @ X0)
% 0.20/0.49          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0))
% 0.20/0.49              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.20/0.49                 (k2_pre_topc @ X0 @ k1_xboole_0))))),
% 0.20/0.49      inference('demod', [status(thm)], ['22', '31'])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k1_tops_1 @ X0 @ (u1_struct_0 @ X0))
% 0.20/0.49            = (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0))
% 0.20/0.49          | ~ (v2_pre_topc @ X0)
% 0.20/0.49          | ~ (l1_pre_topc @ X0)
% 0.20/0.49          | ~ (l1_pre_topc @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['17', '32'])).
% 0.20/0.49  thf('34', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['26', '29'])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k1_tops_1 @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.20/0.49          | ~ (v2_pre_topc @ X0)
% 0.20/0.49          | ~ (l1_pre_topc @ X0)
% 0.20/0.49          | ~ (l1_pre_topc @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (l1_pre_topc @ X0)
% 0.20/0.49          | ~ (v2_pre_topc @ X0)
% 0.20/0.49          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['35'])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k1_tops_1 @ X0 @ (k2_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.20/0.49          | ~ (l1_struct_0 @ X0)
% 0.20/0.49          | ~ (v2_pre_topc @ X0)
% 0.20/0.49          | ~ (l1_pre_topc @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['1', '36'])).
% 0.20/0.49  thf(t43_tops_1, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.49       ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.49          ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t43_tops_1])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (((k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)) != (k2_struct_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      ((((u1_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.20/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.49        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.49        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.49  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(dt_l1_pre_topc, axiom,
% 0.20/0.49    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf('44', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.49      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.49  thf('45', plain, (((u1_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['39', '40', '41', '44'])).
% 0.20/0.49  thf('46', plain,
% 0.20/0.49      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '45'])).
% 0.20/0.49  thf('47', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.49      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.49  thf('48', plain, (((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['46', '47'])).
% 0.20/0.49  thf('49', plain, ($false), inference('simplify', [status(thm)], ['48'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
