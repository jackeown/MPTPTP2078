%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gsKzPVOid1

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 134 expanded)
%              Number of leaves         :   22 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :  563 (1235 expanded)
%              Number of equality atoms :   15 (  24 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(t29_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
            <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_tops_1])).

thf('0',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v4_pre_topc @ X12 @ X13 )
      | ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X13 ) @ ( k2_struct_0 @ X13 ) @ X12 ) @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d6_pre_topc])).

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,
    ( ( ( v3_pre_topc @ ( k7_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['2','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( ( k7_subset_1 @ X6 @ X5 @ X7 )
        = ( k4_xboole_0 @ X5 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('19',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('20',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['11','17','20'])).

thf('22',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('24',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_subset_1 @ X3 @ X4 )
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('25',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,
    ( ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf('30',plain,
    ( ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','30'])).

thf('32',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('33',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('34',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('35',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('36',plain,
    ( ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf('39',plain,
    ( ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('41',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X13 ) @ ( k2_struct_0 @ X13 ) @ X12 ) @ X13 )
      | ( v4_pre_topc @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d6_pre_topc])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_pre_topc @ ( k7_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ sk_B @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf('49',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['45','46','47','48'])).

thf('50',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('51',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','31','32','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gsKzPVOid1
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:00:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 70 iterations in 0.026s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.48  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.20/0.48  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.48  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.48  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.20/0.48  thf(t29_tops_1, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48           ( ( v4_pre_topc @ B @ A ) <=>
% 0.20/0.48             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( l1_pre_topc @ A ) =>
% 0.20/0.48          ( ![B:$i]:
% 0.20/0.48            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48              ( ( v4_pre_topc @ B @ A ) <=>
% 0.20/0.48                ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t29_tops_1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      ((~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.48        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (~ ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) | 
% 0.20/0.48       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf(d3_struct_0, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X11 : $i]:
% 0.20/0.48         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.48        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['3'])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(d6_pre_topc, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48           ( ( v4_pre_topc @ B @ A ) <=>
% 0.20/0.48             ( v3_pre_topc @
% 0.20/0.48               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ 
% 0.20/0.48               A ) ) ) ) ))).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X12 : $i, X13 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.48          | ~ (v4_pre_topc @ X12 @ X13)
% 0.20/0.48          | (v3_pre_topc @ 
% 0.20/0.48             (k7_subset_1 @ (u1_struct_0 @ X13) @ (k2_struct_0 @ X13) @ X12) @ 
% 0.20/0.48             X13)
% 0.20/0.48          | ~ (l1_pre_topc @ X13))),
% 0.20/0.48      inference('cnf', [status(esa)], [d6_pre_topc])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | (v3_pre_topc @ 
% 0.20/0.48           (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.48           sk_A)
% 0.20/0.48        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (((v3_pre_topc @ 
% 0.20/0.48         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.48         sk_A)
% 0.20/0.48        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (((v3_pre_topc @ 
% 0.20/0.48         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.48         sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['4', '9'])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      ((((v3_pre_topc @ 
% 0.20/0.48          (k7_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.48          sk_A)
% 0.20/0.48         | ~ (l1_struct_0 @ sk_A))) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['2', '10'])).
% 0.20/0.48  thf(d10_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.48  thf('13', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.48      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.48  thf(t3_subset, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X8 : $i, X10 : $i]:
% 0.20/0.48         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.48  thf('15', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf(redefinition_k7_subset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.48       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.20/0.48          | ((k7_subset_1 @ X6 @ X5 @ X7) = (k4_xboole_0 @ X5 @ X7)))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.48  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(dt_l1_pre_topc, axiom,
% 0.20/0.48    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.48  thf('20', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (((v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.20/0.48         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['11', '17', '20'])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (![X11 : $i]:
% 0.20/0.48         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(d5_subset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.48       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i]:
% 0.20/0.48         (((k3_subset_1 @ X3 @ X4) = (k4_xboole_0 @ X3 @ X4))
% 0.20/0.48          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 0.20/0.48      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.20/0.48         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      ((~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.20/0.48         <= (~
% 0.20/0.48             ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      ((~ (v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.20/0.48         <= (~
% 0.20/0.48             ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      (((~ (v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.48         | ~ (l1_struct_0 @ sk_A)))
% 0.20/0.48         <= (~
% 0.20/0.48             ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['22', '27'])).
% 0.20/0.48  thf('29', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      ((~ (v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.20/0.48         <= (~
% 0.20/0.48             ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) | 
% 0.20/0.48       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['21', '30'])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) | 
% 0.20/0.48       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.48      inference('split', [status(esa)], ['3'])).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      (![X11 : $i]:
% 0.20/0.48         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.48  thf('34', plain,
% 0.20/0.48      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.20/0.48         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.20/0.48         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['3'])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      (((v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.20/0.48         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['34', '35'])).
% 0.20/0.48  thf('37', plain,
% 0.20/0.48      ((((v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.48         | ~ (l1_struct_0 @ sk_A)))
% 0.20/0.48         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['33', '36'])).
% 0.20/0.48  thf('38', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      (((v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.20/0.48         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['37', '38'])).
% 0.20/0.48  thf('40', plain,
% 0.20/0.48      (![X11 : $i]:
% 0.20/0.48         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.48  thf('41', plain,
% 0.20/0.48      (![X12 : $i, X13 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.48          | ~ (v3_pre_topc @ 
% 0.20/0.48               (k7_subset_1 @ (u1_struct_0 @ X13) @ (k2_struct_0 @ X13) @ X12) @ 
% 0.20/0.48               X13)
% 0.20/0.48          | (v4_pre_topc @ X12 @ X13)
% 0.20/0.48          | ~ (l1_pre_topc @ X13))),
% 0.20/0.48      inference('cnf', [status(esa)], [d6_pre_topc])).
% 0.20/0.48  thf('42', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (v3_pre_topc @ 
% 0.20/0.48             (k7_subset_1 @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0) @ X1) @ X0)
% 0.20/0.48          | ~ (l1_struct_0 @ X0)
% 0.20/0.48          | ~ (l1_pre_topc @ X0)
% 0.20/0.48          | (v4_pre_topc @ X1 @ X0)
% 0.20/0.48          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.48  thf('43', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.48  thf('44', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ X0) @ X1) @ X0)
% 0.20/0.48          | ~ (l1_struct_0 @ X0)
% 0.20/0.48          | ~ (l1_pre_topc @ X0)
% 0.20/0.48          | (v4_pre_topc @ X1 @ X0)
% 0.20/0.48          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.20/0.48      inference('demod', [status(thm)], ['42', '43'])).
% 0.20/0.48  thf('45', plain,
% 0.20/0.48      (((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48         | (v4_pre_topc @ sk_B @ sk_A)
% 0.20/0.48         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48         | ~ (l1_struct_0 @ sk_A)))
% 0.20/0.48         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['39', '44'])).
% 0.20/0.48  thf('46', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('48', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.48  thf('49', plain,
% 0.20/0.48      (((v4_pre_topc @ sk_B @ sk_A))
% 0.20/0.48         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['45', '46', '47', '48'])).
% 0.20/0.48  thf('50', plain,
% 0.20/0.48      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('51', plain,
% 0.20/0.48      (~ ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) | 
% 0.20/0.48       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.48  thf('52', plain, ($false),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['1', '31', '32', '51'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.34/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
