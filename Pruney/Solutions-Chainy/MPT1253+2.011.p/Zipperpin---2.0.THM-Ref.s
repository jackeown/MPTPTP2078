%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UYzbCtr7GK

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:14 EST 2020

% Result     : Theorem 7.76s
% Output     : Refutation 7.76s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 123 expanded)
%              Number of leaves         :   33 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :  573 ( 960 expanded)
%              Number of equality atoms :   30 (  43 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t69_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t69_tops_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ X26 @ ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 )
      | ~ ( r1_tarski @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['3','9'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ~ ( r1_tarski @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('16',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( l1_pre_topc @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X46 @ X47 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('17',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X41: $i,X42: $i] :
      ( ( r1_tarski @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('21',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('23',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X41: $i,X43: $i] :
      ( ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X43 ) )
      | ~ ( r1_tarski @ X41 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X37 ) )
      | ( ( k4_subset_1 @ X37 @ X36 @ X38 )
        = ( k2_xboole_0 @ X36 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) )
      = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['14','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('34',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ( ( k2_pre_topc @ X51 @ X50 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X51 ) @ X50 @ ( k2_tops_1 @ X51 @ X50 ) ) )
      | ~ ( l1_pre_topc @ X51 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
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

thf('38',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( v4_pre_topc @ X44 @ X45 )
      | ( ( k2_pre_topc @ X45 @ X44 )
        = X44 )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( sk_B
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','36','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('45',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','43','44'])).

thf('46',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('47',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r1_tarski @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X21 @ X22 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['45','48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['0','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UYzbCtr7GK
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:46:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 7.76/7.94  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 7.76/7.94  % Solved by: fo/fo7.sh
% 7.76/7.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.76/7.94  % done 12921 iterations in 7.491s
% 7.76/7.94  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 7.76/7.94  % SZS output start Refutation
% 7.76/7.94  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 7.76/7.94  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 7.76/7.94  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 7.76/7.94  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 7.76/7.94  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 7.76/7.94  thf(sk_B_type, type, sk_B: $i).
% 7.76/7.94  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 7.76/7.94  thf(sk_A_type, type, sk_A: $i).
% 7.76/7.94  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 7.76/7.94  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 7.76/7.94  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.76/7.94  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 7.76/7.94  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 7.76/7.94  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 7.76/7.94  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 7.76/7.94  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 7.76/7.94  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 7.76/7.94  thf(t69_tops_1, conjecture,
% 7.76/7.94    (![A:$i]:
% 7.76/7.94     ( ( l1_pre_topc @ A ) =>
% 7.76/7.94       ( ![B:$i]:
% 7.76/7.94         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.76/7.94           ( ( v4_pre_topc @ B @ A ) =>
% 7.76/7.94             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 7.76/7.94  thf(zf_stmt_0, negated_conjecture,
% 7.76/7.94    (~( ![A:$i]:
% 7.76/7.94        ( ( l1_pre_topc @ A ) =>
% 7.76/7.94          ( ![B:$i]:
% 7.76/7.94            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.76/7.94              ( ( v4_pre_topc @ B @ A ) =>
% 7.76/7.94                ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ) )),
% 7.76/7.94    inference('cnf.neg', [status(esa)], [t69_tops_1])).
% 7.76/7.94  thf('0', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 7.76/7.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.76/7.94  thf(t7_xboole_1, axiom,
% 7.76/7.94    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 7.76/7.94  thf('1', plain,
% 7.76/7.94      (![X26 : $i, X27 : $i]: (r1_tarski @ X26 @ (k2_xboole_0 @ X26 @ X27))),
% 7.76/7.94      inference('cnf', [status(esa)], [t7_xboole_1])).
% 7.76/7.94  thf(t43_xboole_1, axiom,
% 7.76/7.94    (![A:$i,B:$i,C:$i]:
% 7.76/7.94     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 7.76/7.94       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 7.76/7.94  thf('2', plain,
% 7.76/7.94      (![X18 : $i, X19 : $i, X20 : $i]:
% 7.76/7.94         ((r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X20)
% 7.76/7.94          | ~ (r1_tarski @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 7.76/7.94      inference('cnf', [status(esa)], [t43_xboole_1])).
% 7.76/7.94  thf('3', plain,
% 7.76/7.94      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 7.76/7.94      inference('sup-', [status(thm)], ['1', '2'])).
% 7.76/7.94  thf(d10_xboole_0, axiom,
% 7.76/7.94    (![A:$i,B:$i]:
% 7.76/7.94     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 7.76/7.94  thf('4', plain,
% 7.76/7.94      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 7.76/7.94      inference('cnf', [status(esa)], [d10_xboole_0])).
% 7.76/7.94  thf('5', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 7.76/7.94      inference('simplify', [status(thm)], ['4'])).
% 7.76/7.94  thf(t28_xboole_1, axiom,
% 7.76/7.94    (![A:$i,B:$i]:
% 7.76/7.94     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 7.76/7.94  thf('6', plain,
% 7.76/7.94      (![X10 : $i, X11 : $i]:
% 7.76/7.94         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 7.76/7.94      inference('cnf', [status(esa)], [t28_xboole_1])).
% 7.76/7.94  thf('7', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 7.76/7.94      inference('sup-', [status(thm)], ['5', '6'])).
% 7.76/7.94  thf(t100_xboole_1, axiom,
% 7.76/7.94    (![A:$i,B:$i]:
% 7.76/7.94     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 7.76/7.94  thf('8', plain,
% 7.76/7.94      (![X3 : $i, X4 : $i]:
% 7.76/7.94         ((k4_xboole_0 @ X3 @ X4)
% 7.76/7.94           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 7.76/7.94      inference('cnf', [status(esa)], [t100_xboole_1])).
% 7.76/7.94  thf('9', plain,
% 7.76/7.94      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 7.76/7.94      inference('sup+', [status(thm)], ['7', '8'])).
% 7.76/7.94  thf('10', plain,
% 7.76/7.94      (![X0 : $i, X1 : $i]: (r1_tarski @ (k5_xboole_0 @ X1 @ X1) @ X0)),
% 7.76/7.94      inference('demod', [status(thm)], ['3', '9'])).
% 7.76/7.94  thf(t38_xboole_1, axiom,
% 7.76/7.94    (![A:$i,B:$i]:
% 7.76/7.94     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 7.76/7.94       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 7.76/7.94  thf('11', plain,
% 7.76/7.94      (![X14 : $i, X15 : $i]:
% 7.76/7.94         (((X14) = (k1_xboole_0))
% 7.76/7.94          | ~ (r1_tarski @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 7.76/7.94      inference('cnf', [status(esa)], [t38_xboole_1])).
% 7.76/7.94  thf('12', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 7.76/7.94      inference('sup-', [status(thm)], ['10', '11'])).
% 7.76/7.94  thf(t3_boole, axiom,
% 7.76/7.94    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 7.76/7.94  thf('13', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 7.76/7.94      inference('cnf', [status(esa)], [t3_boole])).
% 7.76/7.94  thf('14', plain,
% 7.76/7.94      (![X0 : $i, X1 : $i]:
% 7.76/7.94         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 7.76/7.94      inference('sup+', [status(thm)], ['12', '13'])).
% 7.76/7.94  thf('15', plain,
% 7.76/7.94      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.76/7.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.76/7.94  thf(dt_k2_tops_1, axiom,
% 7.76/7.94    (![A:$i,B:$i]:
% 7.76/7.94     ( ( ( l1_pre_topc @ A ) & 
% 7.76/7.94         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 7.76/7.94       ( m1_subset_1 @
% 7.76/7.94         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 7.76/7.94  thf('16', plain,
% 7.76/7.94      (![X46 : $i, X47 : $i]:
% 7.76/7.94         (~ (l1_pre_topc @ X46)
% 7.76/7.94          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 7.76/7.94          | (m1_subset_1 @ (k2_tops_1 @ X46 @ X47) @ 
% 7.76/7.94             (k1_zfmisc_1 @ (u1_struct_0 @ X46))))),
% 7.76/7.94      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 7.76/7.94  thf('17', plain,
% 7.76/7.94      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 7.76/7.94         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.76/7.94        | ~ (l1_pre_topc @ sk_A))),
% 7.76/7.94      inference('sup-', [status(thm)], ['15', '16'])).
% 7.76/7.94  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 7.76/7.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.76/7.94  thf('19', plain,
% 7.76/7.94      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 7.76/7.94        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.76/7.94      inference('demod', [status(thm)], ['17', '18'])).
% 7.76/7.94  thf(t3_subset, axiom,
% 7.76/7.94    (![A:$i,B:$i]:
% 7.76/7.94     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 7.76/7.94  thf('20', plain,
% 7.76/7.94      (![X41 : $i, X42 : $i]:
% 7.76/7.94         ((r1_tarski @ X41 @ X42) | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42)))),
% 7.76/7.94      inference('cnf', [status(esa)], [t3_subset])).
% 7.76/7.94  thf('21', plain,
% 7.76/7.94      ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 7.76/7.94      inference('sup-', [status(thm)], ['19', '20'])).
% 7.76/7.94  thf(t36_xboole_1, axiom,
% 7.76/7.94    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 7.76/7.94  thf('22', plain,
% 7.76/7.94      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 7.76/7.94      inference('cnf', [status(esa)], [t36_xboole_1])).
% 7.76/7.94  thf(t1_xboole_1, axiom,
% 7.76/7.94    (![A:$i,B:$i,C:$i]:
% 7.76/7.94     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 7.76/7.94       ( r1_tarski @ A @ C ) ))).
% 7.76/7.94  thf('23', plain,
% 7.76/7.94      (![X7 : $i, X8 : $i, X9 : $i]:
% 7.76/7.94         (~ (r1_tarski @ X7 @ X8)
% 7.76/7.94          | ~ (r1_tarski @ X8 @ X9)
% 7.76/7.94          | (r1_tarski @ X7 @ X9))),
% 7.76/7.94      inference('cnf', [status(esa)], [t1_xboole_1])).
% 7.76/7.94  thf('24', plain,
% 7.76/7.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.76/7.94         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 7.76/7.94      inference('sup-', [status(thm)], ['22', '23'])).
% 7.76/7.94  thf('25', plain,
% 7.76/7.94      (![X0 : $i]:
% 7.76/7.94         (r1_tarski @ (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0) @ 
% 7.76/7.94          (u1_struct_0 @ sk_A))),
% 7.76/7.94      inference('sup-', [status(thm)], ['21', '24'])).
% 7.76/7.94  thf('26', plain,
% 7.76/7.94      (![X41 : $i, X43 : $i]:
% 7.76/7.94         ((m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X43)) | ~ (r1_tarski @ X41 @ X43))),
% 7.76/7.94      inference('cnf', [status(esa)], [t3_subset])).
% 7.76/7.94  thf('27', plain,
% 7.76/7.94      (![X0 : $i]:
% 7.76/7.94         (m1_subset_1 @ (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0) @ 
% 7.76/7.94          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.76/7.94      inference('sup-', [status(thm)], ['25', '26'])).
% 7.76/7.94  thf('28', plain,
% 7.76/7.94      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.76/7.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.76/7.94  thf(redefinition_k4_subset_1, axiom,
% 7.76/7.94    (![A:$i,B:$i,C:$i]:
% 7.76/7.94     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 7.76/7.94         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 7.76/7.94       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 7.76/7.94  thf('29', plain,
% 7.76/7.94      (![X36 : $i, X37 : $i, X38 : $i]:
% 7.76/7.94         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 7.76/7.94          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X37))
% 7.76/7.94          | ((k4_subset_1 @ X37 @ X36 @ X38) = (k2_xboole_0 @ X36 @ X38)))),
% 7.76/7.94      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 7.76/7.94  thf('30', plain,
% 7.76/7.94      (![X0 : $i]:
% 7.76/7.94         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 7.76/7.94            = (k2_xboole_0 @ sk_B @ X0))
% 7.76/7.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 7.76/7.94      inference('sup-', [status(thm)], ['28', '29'])).
% 7.76/7.94  thf('31', plain,
% 7.76/7.94      (![X0 : $i]:
% 7.76/7.94         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 7.76/7.94           (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0))
% 7.76/7.94           = (k2_xboole_0 @ sk_B @ 
% 7.76/7.94              (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0)))),
% 7.76/7.94      inference('sup-', [status(thm)], ['27', '30'])).
% 7.76/7.94  thf('32', plain,
% 7.76/7.94      (![X0 : $i]:
% 7.76/7.94         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 7.76/7.94           (k2_tops_1 @ sk_A @ sk_B))
% 7.76/7.94           = (k2_xboole_0 @ sk_B @ 
% 7.76/7.94              (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 7.76/7.94               (k5_xboole_0 @ X0 @ X0))))),
% 7.76/7.94      inference('sup+', [status(thm)], ['14', '31'])).
% 7.76/7.94  thf('33', plain,
% 7.76/7.94      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.76/7.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.76/7.94  thf(t65_tops_1, axiom,
% 7.76/7.94    (![A:$i]:
% 7.76/7.94     ( ( l1_pre_topc @ A ) =>
% 7.76/7.94       ( ![B:$i]:
% 7.76/7.94         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.76/7.94           ( ( k2_pre_topc @ A @ B ) =
% 7.76/7.94             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 7.76/7.94  thf('34', plain,
% 7.76/7.94      (![X50 : $i, X51 : $i]:
% 7.76/7.94         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 7.76/7.94          | ((k2_pre_topc @ X51 @ X50)
% 7.76/7.94              = (k4_subset_1 @ (u1_struct_0 @ X51) @ X50 @ 
% 7.76/7.94                 (k2_tops_1 @ X51 @ X50)))
% 7.76/7.94          | ~ (l1_pre_topc @ X51))),
% 7.76/7.94      inference('cnf', [status(esa)], [t65_tops_1])).
% 7.76/7.94  thf('35', plain,
% 7.76/7.94      ((~ (l1_pre_topc @ sk_A)
% 7.76/7.94        | ((k2_pre_topc @ sk_A @ sk_B)
% 7.76/7.94            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 7.76/7.94               (k2_tops_1 @ sk_A @ sk_B))))),
% 7.76/7.94      inference('sup-', [status(thm)], ['33', '34'])).
% 7.76/7.94  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 7.76/7.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.76/7.94  thf('37', plain,
% 7.76/7.94      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.76/7.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.76/7.94  thf(t52_pre_topc, axiom,
% 7.76/7.94    (![A:$i]:
% 7.76/7.94     ( ( l1_pre_topc @ A ) =>
% 7.76/7.94       ( ![B:$i]:
% 7.76/7.94         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.76/7.94           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 7.76/7.94             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 7.76/7.94               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 7.76/7.94  thf('38', plain,
% 7.76/7.94      (![X44 : $i, X45 : $i]:
% 7.76/7.94         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 7.76/7.94          | ~ (v4_pre_topc @ X44 @ X45)
% 7.76/7.94          | ((k2_pre_topc @ X45 @ X44) = (X44))
% 7.76/7.94          | ~ (l1_pre_topc @ X45))),
% 7.76/7.94      inference('cnf', [status(esa)], [t52_pre_topc])).
% 7.76/7.94  thf('39', plain,
% 7.76/7.94      ((~ (l1_pre_topc @ sk_A)
% 7.76/7.94        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 7.76/7.94        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 7.76/7.94      inference('sup-', [status(thm)], ['37', '38'])).
% 7.76/7.94  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 7.76/7.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.76/7.94  thf('41', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 7.76/7.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.76/7.94  thf('42', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 7.76/7.94      inference('demod', [status(thm)], ['39', '40', '41'])).
% 7.76/7.94  thf('43', plain,
% 7.76/7.94      (((sk_B)
% 7.76/7.94         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 7.76/7.94            (k2_tops_1 @ sk_A @ sk_B)))),
% 7.76/7.94      inference('demod', [status(thm)], ['35', '36', '42'])).
% 7.76/7.94  thf('44', plain,
% 7.76/7.94      (![X0 : $i, X1 : $i]:
% 7.76/7.94         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 7.76/7.94      inference('sup+', [status(thm)], ['12', '13'])).
% 7.76/7.94  thf('45', plain,
% 7.76/7.94      (((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 7.76/7.94      inference('demod', [status(thm)], ['32', '43', '44'])).
% 7.76/7.94  thf('46', plain,
% 7.76/7.94      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 7.76/7.94      inference('cnf', [status(esa)], [t36_xboole_1])).
% 7.76/7.94  thf(t44_xboole_1, axiom,
% 7.76/7.94    (![A:$i,B:$i,C:$i]:
% 7.76/7.94     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 7.76/7.94       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 7.76/7.94  thf('47', plain,
% 7.76/7.94      (![X21 : $i, X22 : $i, X23 : $i]:
% 7.76/7.94         ((r1_tarski @ X21 @ (k2_xboole_0 @ X22 @ X23))
% 7.76/7.94          | ~ (r1_tarski @ (k4_xboole_0 @ X21 @ X22) @ X23))),
% 7.76/7.94      inference('cnf', [status(esa)], [t44_xboole_1])).
% 7.76/7.94  thf('48', plain,
% 7.76/7.94      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 7.76/7.94      inference('sup-', [status(thm)], ['46', '47'])).
% 7.76/7.94  thf('49', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 7.76/7.94      inference('sup+', [status(thm)], ['45', '48'])).
% 7.76/7.94  thf('50', plain, ($false), inference('demod', [status(thm)], ['0', '49'])).
% 7.76/7.94  
% 7.76/7.94  % SZS output end Refutation
% 7.76/7.94  
% 7.76/7.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
