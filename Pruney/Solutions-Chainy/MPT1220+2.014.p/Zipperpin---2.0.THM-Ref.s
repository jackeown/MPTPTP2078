%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IMsx6LwSBp

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:41 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 136 expanded)
%              Number of leaves         :   30 (  53 expanded)
%              Depth                    :   16
%              Number of atoms          :  447 ( 810 expanded)
%              Number of equality atoms :   31 (  65 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(fc3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X17: $i] :
      ( ( v1_xboole_0 @ ( k1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc3_struct_0])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('1',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ X6 )
      | ( X5 = X6 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( k1_xboole_0
        = ( k1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t27_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_struct_0 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X18 ) @ ( k1_struct_0 @ X18 ) ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t27_pre_topc])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('8',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','14'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('17',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X10 ) @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('18',plain,(
    ! [X7: $i] :
      ( ( k2_subset_1 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('19',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('20',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','23'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('25',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','14'])).

thf('28',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('29',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( r1_tarski @ X19 @ ( k2_pre_topc @ X20 @ X19 ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf(t27_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) )
        = ( k2_struct_0 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) )
          = ( k2_struct_0 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_tops_1])).

thf('38',plain,(
    ( k2_pre_topc @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( ( u1_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ( u1_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('45',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ( k2_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','45'])).

thf('47',plain,(
    $false ),
    inference(simplify,[status(thm)],['46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IMsx6LwSBp
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:44:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.48/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.48/0.68  % Solved by: fo/fo7.sh
% 0.48/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.68  % done 418 iterations in 0.225s
% 0.48/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.48/0.68  % SZS output start Refutation
% 0.48/0.68  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.48/0.68  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.48/0.68  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.48/0.68  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 0.48/0.68  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.48/0.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.48/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.48/0.68  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.48/0.68  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.48/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.48/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.48/0.68  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.48/0.68  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.48/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.48/0.68  thf(fc3_struct_0, axiom,
% 0.48/0.68    (![A:$i]: ( ( l1_struct_0 @ A ) => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ))).
% 0.48/0.68  thf('0', plain,
% 0.48/0.68      (![X17 : $i]:
% 0.48/0.68         ((v1_xboole_0 @ (k1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.48/0.68      inference('cnf', [status(esa)], [fc3_struct_0])).
% 0.48/0.68  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.48/0.68  thf('1', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.48/0.68      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.48/0.68  thf(t8_boole, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.48/0.68  thf('2', plain,
% 0.48/0.68      (![X5 : $i, X6 : $i]:
% 0.48/0.68         (~ (v1_xboole_0 @ X5) | ~ (v1_xboole_0 @ X6) | ((X5) = (X6)))),
% 0.48/0.68      inference('cnf', [status(esa)], [t8_boole])).
% 0.48/0.68  thf('3', plain,
% 0.48/0.68      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.48/0.68      inference('sup-', [status(thm)], ['1', '2'])).
% 0.48/0.68  thf('4', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (~ (l1_struct_0 @ X0) | ((k1_xboole_0) = (k1_struct_0 @ X0)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['0', '3'])).
% 0.48/0.68  thf(t27_pre_topc, axiom,
% 0.48/0.68    (![A:$i]:
% 0.48/0.68     ( ( l1_struct_0 @ A ) =>
% 0.48/0.68       ( ( k2_struct_0 @ A ) =
% 0.48/0.68         ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_struct_0 @ A ) ) ) ))).
% 0.48/0.68  thf('5', plain,
% 0.48/0.68      (![X18 : $i]:
% 0.48/0.68         (((k2_struct_0 @ X18)
% 0.48/0.68            = (k3_subset_1 @ (u1_struct_0 @ X18) @ (k1_struct_0 @ X18)))
% 0.48/0.68          | ~ (l1_struct_0 @ X18))),
% 0.48/0.68      inference('cnf', [status(esa)], [t27_pre_topc])).
% 0.48/0.68  thf('6', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (((k2_struct_0 @ X0)
% 0.48/0.68            = (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0))
% 0.48/0.68          | ~ (l1_struct_0 @ X0)
% 0.48/0.68          | ~ (l1_struct_0 @ X0))),
% 0.48/0.68      inference('sup+', [status(thm)], ['4', '5'])).
% 0.48/0.68  thf('7', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (~ (l1_struct_0 @ X0)
% 0.48/0.68          | ((k2_struct_0 @ X0)
% 0.48/0.68              = (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0)))),
% 0.48/0.68      inference('simplify', [status(thm)], ['6'])).
% 0.48/0.68  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.48/0.68  thf('8', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.48/0.68      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.48/0.68  thf(t3_subset, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.48/0.68  thf('9', plain,
% 0.48/0.68      (![X11 : $i, X13 : $i]:
% 0.48/0.68         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.48/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.48/0.68  thf('10', plain,
% 0.48/0.68      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.48/0.68      inference('sup-', [status(thm)], ['8', '9'])).
% 0.48/0.68  thf(d5_subset_1, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.68       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.48/0.68  thf('11', plain,
% 0.48/0.68      (![X8 : $i, X9 : $i]:
% 0.48/0.68         (((k3_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))
% 0.48/0.68          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.48/0.68      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.48/0.68  thf('12', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.48/0.68      inference('sup-', [status(thm)], ['10', '11'])).
% 0.48/0.68  thf(t3_boole, axiom,
% 0.48/0.68    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.48/0.68  thf('13', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.48/0.68      inference('cnf', [status(esa)], [t3_boole])).
% 0.48/0.68  thf('14', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.48/0.68      inference('demod', [status(thm)], ['12', '13'])).
% 0.48/0.68  thf('15', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (~ (l1_struct_0 @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 0.48/0.68      inference('demod', [status(thm)], ['7', '14'])).
% 0.48/0.68  thf('16', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (~ (l1_struct_0 @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 0.48/0.68      inference('demod', [status(thm)], ['7', '14'])).
% 0.48/0.68  thf(dt_k2_subset_1, axiom,
% 0.48/0.68    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.48/0.68  thf('17', plain,
% 0.48/0.68      (![X10 : $i]: (m1_subset_1 @ (k2_subset_1 @ X10) @ (k1_zfmisc_1 @ X10))),
% 0.48/0.68      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.48/0.68  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.48/0.68  thf('18', plain, (![X7 : $i]: ((k2_subset_1 @ X7) = (X7))),
% 0.48/0.68      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.48/0.68  thf('19', plain, (![X10 : $i]: (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X10))),
% 0.48/0.68      inference('demod', [status(thm)], ['17', '18'])).
% 0.48/0.68  thf(dt_k2_pre_topc, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( ( l1_pre_topc @ A ) & 
% 0.48/0.68         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.48/0.68       ( m1_subset_1 @
% 0.48/0.68         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.48/0.68  thf('20', plain,
% 0.48/0.68      (![X14 : $i, X15 : $i]:
% 0.48/0.68         (~ (l1_pre_topc @ X14)
% 0.48/0.68          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.48/0.68          | (m1_subset_1 @ (k2_pre_topc @ X14 @ X15) @ 
% 0.48/0.68             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 0.48/0.68      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.48/0.68  thf('21', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         ((m1_subset_1 @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 0.48/0.68           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.48/0.68          | ~ (l1_pre_topc @ X0))),
% 0.48/0.68      inference('sup-', [status(thm)], ['19', '20'])).
% 0.48/0.68  thf('22', plain,
% 0.48/0.68      (![X11 : $i, X12 : $i]:
% 0.48/0.68         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.48/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.48/0.68  thf('23', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (~ (l1_pre_topc @ X0)
% 0.48/0.68          | (r1_tarski @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 0.48/0.68             (u1_struct_0 @ X0)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['21', '22'])).
% 0.48/0.68  thf('24', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         ((r1_tarski @ (k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) @ 
% 0.48/0.68           (u1_struct_0 @ X0))
% 0.48/0.68          | ~ (l1_struct_0 @ X0)
% 0.48/0.68          | ~ (l1_pre_topc @ X0))),
% 0.48/0.68      inference('sup+', [status(thm)], ['16', '23'])).
% 0.48/0.68  thf(dt_l1_pre_topc, axiom,
% 0.48/0.68    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.48/0.68  thf('25', plain,
% 0.48/0.68      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_pre_topc @ X16))),
% 0.48/0.68      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.48/0.68  thf('26', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (~ (l1_pre_topc @ X0)
% 0.48/0.68          | (r1_tarski @ (k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) @ 
% 0.48/0.68             (u1_struct_0 @ X0)))),
% 0.48/0.68      inference('clc', [status(thm)], ['24', '25'])).
% 0.48/0.68  thf('27', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (~ (l1_struct_0 @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 0.48/0.68      inference('demod', [status(thm)], ['7', '14'])).
% 0.48/0.68  thf('28', plain, (![X10 : $i]: (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X10))),
% 0.48/0.68      inference('demod', [status(thm)], ['17', '18'])).
% 0.48/0.68  thf(t48_pre_topc, axiom,
% 0.48/0.68    (![A:$i]:
% 0.48/0.68     ( ( l1_pre_topc @ A ) =>
% 0.48/0.68       ( ![B:$i]:
% 0.48/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.68           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.48/0.68  thf('29', plain,
% 0.48/0.68      (![X19 : $i, X20 : $i]:
% 0.48/0.68         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.48/0.68          | (r1_tarski @ X19 @ (k2_pre_topc @ X20 @ X19))
% 0.48/0.68          | ~ (l1_pre_topc @ X20))),
% 0.48/0.68      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.48/0.68  thf('30', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (~ (l1_pre_topc @ X0)
% 0.48/0.68          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.48/0.68             (k2_pre_topc @ X0 @ (u1_struct_0 @ X0))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['28', '29'])).
% 0.48/0.68  thf('31', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         ((r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.48/0.68           (k2_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 0.48/0.68          | ~ (l1_struct_0 @ X0)
% 0.48/0.68          | ~ (l1_pre_topc @ X0))),
% 0.48/0.68      inference('sup+', [status(thm)], ['27', '30'])).
% 0.48/0.68  thf('32', plain,
% 0.48/0.68      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_pre_topc @ X16))),
% 0.48/0.68      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.48/0.68  thf('33', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (~ (l1_pre_topc @ X0)
% 0.48/0.68          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.48/0.68             (k2_pre_topc @ X0 @ (k2_struct_0 @ X0))))),
% 0.48/0.68      inference('clc', [status(thm)], ['31', '32'])).
% 0.48/0.68  thf(d10_xboole_0, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.48/0.68  thf('34', plain,
% 0.48/0.68      (![X0 : $i, X2 : $i]:
% 0.48/0.68         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.48/0.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.48/0.68  thf('35', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (~ (l1_pre_topc @ X0)
% 0.48/0.68          | ~ (r1_tarski @ (k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) @ 
% 0.48/0.68               (u1_struct_0 @ X0))
% 0.48/0.68          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (u1_struct_0 @ X0)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['33', '34'])).
% 0.48/0.68  thf('36', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (~ (l1_pre_topc @ X0)
% 0.48/0.68          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.48/0.68          | ~ (l1_pre_topc @ X0))),
% 0.48/0.68      inference('sup-', [status(thm)], ['26', '35'])).
% 0.48/0.68  thf('37', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.48/0.68          | ~ (l1_pre_topc @ X0))),
% 0.48/0.68      inference('simplify', [status(thm)], ['36'])).
% 0.48/0.68  thf(t27_tops_1, conjecture,
% 0.48/0.68    (![A:$i]:
% 0.48/0.68     ( ( l1_pre_topc @ A ) =>
% 0.48/0.68       ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.48/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.68    (~( ![A:$i]:
% 0.48/0.68        ( ( l1_pre_topc @ A ) =>
% 0.48/0.68          ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ) )),
% 0.48/0.68    inference('cnf.neg', [status(esa)], [t27_tops_1])).
% 0.48/0.68  thf('38', plain,
% 0.48/0.68      (((k2_pre_topc @ sk_A @ (k2_struct_0 @ sk_A)) != (k2_struct_0 @ sk_A))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('39', plain,
% 0.48/0.68      ((((u1_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)) | ~ (l1_pre_topc @ sk_A))),
% 0.48/0.68      inference('sup-', [status(thm)], ['37', '38'])).
% 0.48/0.68  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('41', plain, (((u1_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.48/0.68      inference('demod', [status(thm)], ['39', '40'])).
% 0.48/0.68  thf('42', plain,
% 0.48/0.68      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.48/0.68      inference('sup-', [status(thm)], ['15', '41'])).
% 0.48/0.68  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('44', plain,
% 0.48/0.68      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_pre_topc @ X16))),
% 0.48/0.68      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.48/0.68  thf('45', plain, ((l1_struct_0 @ sk_A)),
% 0.48/0.68      inference('sup-', [status(thm)], ['43', '44'])).
% 0.48/0.68  thf('46', plain, (((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.48/0.68      inference('demod', [status(thm)], ['42', '45'])).
% 0.48/0.68  thf('47', plain, ($false), inference('simplify', [status(thm)], ['46'])).
% 0.48/0.68  
% 0.48/0.68  % SZS output end Refutation
% 0.48/0.68  
% 0.48/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
