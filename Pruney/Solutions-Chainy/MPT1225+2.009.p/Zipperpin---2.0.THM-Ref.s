%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4p3niqiyEU

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:47 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 136 expanded)
%              Number of leaves         :   22 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :  600 (2309 expanded)
%              Number of equality atoms :   25 (  83 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(t34_tops_1,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v4_pre_topc @ B @ A )
                    & ( v4_pre_topc @ C @ A ) )
                 => ( ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) )
                    = ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t51_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( r1_tarski @ ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ X17 @ ( k9_subset_1 @ ( u1_struct_0 @ X17 ) @ X16 @ X18 ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ X17 ) @ ( k2_pre_topc @ X17 @ X16 ) @ ( k2_pre_topc @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t51_pre_topc])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
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

thf('6',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v4_pre_topc @ X19 @ X20 )
      | ( ( k2_pre_topc @ X20 @ X19 )
        = X19 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['3','4','10'])).

thf('12',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k9_subset_1 @ X10 @ X8 @ X9 )
        = ( k3_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v4_pre_topc @ X19 @ X20 )
      | ( ( k2_pre_topc @ X20 @ X19 )
        = X19 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
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

thf('22',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('23',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['12','15','21','22'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,
    ( ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) )
    | ( ( k3_xboole_0 @ sk_B @ sk_C )
      = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('27',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('28',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('29',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('30',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('35',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( r1_tarski @ X14 @ ( k2_pre_topc @ X15 @ X14 ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['25','38'])).

thf('40',plain,(
    ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) )
 != ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('42',plain,(
    ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) )
 != ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('44',plain,
    ( ( k2_pre_topc @ sk_A @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('46',plain,(
    ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
 != ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['39','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4p3niqiyEU
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:13:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.38/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.61  % Solved by: fo/fo7.sh
% 0.38/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.61  % done 288 iterations in 0.166s
% 0.38/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.61  % SZS output start Refutation
% 0.38/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.61  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.38/0.61  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.61  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.38/0.61  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.38/0.61  thf(t34_tops_1, conjecture,
% 0.38/0.61    (![A:$i]:
% 0.38/0.61     ( ( l1_pre_topc @ A ) =>
% 0.38/0.61       ( ![B:$i]:
% 0.38/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.61           ( ![C:$i]:
% 0.38/0.61             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.61               ( ( ( v4_pre_topc @ B @ A ) & ( v4_pre_topc @ C @ A ) ) =>
% 0.38/0.61                 ( ( k2_pre_topc @
% 0.38/0.61                     A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) =
% 0.38/0.61                   ( k9_subset_1 @
% 0.38/0.61                     ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.38/0.61                     ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.38/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.61    (~( ![A:$i]:
% 0.38/0.61        ( ( l1_pre_topc @ A ) =>
% 0.38/0.61          ( ![B:$i]:
% 0.38/0.61            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.61              ( ![C:$i]:
% 0.38/0.61                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.61                  ( ( ( v4_pre_topc @ B @ A ) & ( v4_pre_topc @ C @ A ) ) =>
% 0.38/0.61                    ( ( k2_pre_topc @
% 0.38/0.61                        A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) =
% 0.38/0.61                      ( k9_subset_1 @
% 0.38/0.61                        ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.38/0.61                        ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ) ) )),
% 0.38/0.61    inference('cnf.neg', [status(esa)], [t34_tops_1])).
% 0.38/0.61  thf('0', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('1', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(t51_pre_topc, axiom,
% 0.38/0.61    (![A:$i]:
% 0.38/0.61     ( ( l1_pre_topc @ A ) =>
% 0.38/0.61       ( ![B:$i]:
% 0.38/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.61           ( ![C:$i]:
% 0.38/0.61             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.61               ( r1_tarski @
% 0.38/0.61                 ( k2_pre_topc @
% 0.38/0.61                   A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 0.38/0.61                 ( k9_subset_1 @
% 0.38/0.61                   ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.38/0.61                   ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 0.38/0.61  thf('2', plain,
% 0.38/0.61      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.38/0.61          | (r1_tarski @ 
% 0.38/0.61             (k2_pre_topc @ X17 @ 
% 0.38/0.61              (k9_subset_1 @ (u1_struct_0 @ X17) @ X16 @ X18)) @ 
% 0.38/0.61             (k9_subset_1 @ (u1_struct_0 @ X17) @ (k2_pre_topc @ X17 @ X16) @ 
% 0.38/0.61              (k2_pre_topc @ X17 @ X18)))
% 0.38/0.61          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.38/0.61          | ~ (l1_pre_topc @ X17))),
% 0.38/0.61      inference('cnf', [status(esa)], [t51_pre_topc])).
% 0.38/0.61  thf('3', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (l1_pre_topc @ sk_A)
% 0.38/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.61          | (r1_tarski @ 
% 0.38/0.61             (k2_pre_topc @ sk_A @ 
% 0.38/0.61              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)) @ 
% 0.38/0.61             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.61              (k2_pre_topc @ sk_A @ sk_B) @ (k2_pre_topc @ sk_A @ X0))))),
% 0.38/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.61  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('5', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(t52_pre_topc, axiom,
% 0.38/0.61    (![A:$i]:
% 0.38/0.61     ( ( l1_pre_topc @ A ) =>
% 0.38/0.61       ( ![B:$i]:
% 0.38/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.61           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.38/0.61             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.38/0.61               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.38/0.61  thf('6', plain,
% 0.38/0.61      (![X19 : $i, X20 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.38/0.61          | ~ (v4_pre_topc @ X19 @ X20)
% 0.38/0.61          | ((k2_pre_topc @ X20 @ X19) = (X19))
% 0.38/0.61          | ~ (l1_pre_topc @ X20))),
% 0.38/0.61      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.38/0.61  thf('7', plain,
% 0.38/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.61        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.38/0.61        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.61      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.61  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('9', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('10', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.38/0.61      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.38/0.61  thf('11', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.61          | (r1_tarski @ 
% 0.38/0.61             (k2_pre_topc @ sk_A @ 
% 0.38/0.61              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)) @ 
% 0.38/0.61             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.61              (k2_pre_topc @ sk_A @ X0))))),
% 0.38/0.61      inference('demod', [status(thm)], ['3', '4', '10'])).
% 0.38/0.61  thf('12', plain,
% 0.38/0.61      ((r1_tarski @ 
% 0.38/0.61        (k2_pre_topc @ sk_A @ 
% 0.38/0.61         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)) @ 
% 0.38/0.61        (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.61         (k2_pre_topc @ sk_A @ sk_C)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['0', '11'])).
% 0.38/0.61  thf('13', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(redefinition_k9_subset_1, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i]:
% 0.38/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.61       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.38/0.61  thf('14', plain,
% 0.38/0.61      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.38/0.61         (((k9_subset_1 @ X10 @ X8 @ X9) = (k3_xboole_0 @ X8 @ X9))
% 0.38/0.61          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.38/0.61      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.38/0.61  thf('15', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.38/0.61           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.38/0.61      inference('sup-', [status(thm)], ['13', '14'])).
% 0.38/0.61  thf('16', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('17', plain,
% 0.38/0.61      (![X19 : $i, X20 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.38/0.61          | ~ (v4_pre_topc @ X19 @ X20)
% 0.38/0.61          | ((k2_pre_topc @ X20 @ X19) = (X19))
% 0.38/0.61          | ~ (l1_pre_topc @ X20))),
% 0.38/0.61      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.38/0.61  thf('18', plain,
% 0.38/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.61        | ((k2_pre_topc @ sk_A @ sk_C) = (sk_C))
% 0.38/0.61        | ~ (v4_pre_topc @ sk_C @ sk_A))),
% 0.38/0.61      inference('sup-', [status(thm)], ['16', '17'])).
% 0.38/0.61  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('20', plain, ((v4_pre_topc @ sk_C @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('21', plain, (((k2_pre_topc @ sk_A @ sk_C) = (sk_C))),
% 0.38/0.61      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.38/0.61  thf('22', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.38/0.61           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.38/0.61      inference('sup-', [status(thm)], ['13', '14'])).
% 0.38/0.61  thf('23', plain,
% 0.38/0.61      ((r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 0.38/0.61        (k3_xboole_0 @ sk_B @ sk_C))),
% 0.38/0.61      inference('demod', [status(thm)], ['12', '15', '21', '22'])).
% 0.38/0.61  thf(d10_xboole_0, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.61  thf('24', plain,
% 0.38/0.61      (![X0 : $i, X2 : $i]:
% 0.38/0.61         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.38/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.61  thf('25', plain,
% 0.38/0.61      ((~ (r1_tarski @ (k3_xboole_0 @ sk_B @ sk_C) @ 
% 0.38/0.61           (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))
% 0.38/0.61        | ((k3_xboole_0 @ sk_B @ sk_C)
% 0.38/0.61            = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 0.38/0.61      inference('sup-', [status(thm)], ['23', '24'])).
% 0.38/0.61  thf('26', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(t3_subset, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.61  thf('27', plain,
% 0.38/0.61      (![X11 : $i, X12 : $i]:
% 0.38/0.61         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.38/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.61  thf('28', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.38/0.61      inference('sup-', [status(thm)], ['26', '27'])).
% 0.38/0.61  thf(t17_xboole_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.38/0.61  thf('29', plain,
% 0.38/0.61      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 0.38/0.61      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.38/0.61  thf(t1_xboole_1, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i]:
% 0.38/0.61     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.38/0.61       ( r1_tarski @ A @ C ) ))).
% 0.38/0.61  thf('30', plain,
% 0.38/0.61      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.38/0.61         (~ (r1_tarski @ X5 @ X6)
% 0.38/0.61          | ~ (r1_tarski @ X6 @ X7)
% 0.38/0.61          | (r1_tarski @ X5 @ X7))),
% 0.38/0.61      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.38/0.61  thf('31', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.61         ((r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.38/0.61      inference('sup-', [status(thm)], ['29', '30'])).
% 0.38/0.61  thf('32', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 0.38/0.61      inference('sup-', [status(thm)], ['28', '31'])).
% 0.38/0.61  thf('33', plain,
% 0.38/0.61      (![X11 : $i, X13 : $i]:
% 0.38/0.61         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.38/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.61  thf('34', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 0.38/0.61          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['32', '33'])).
% 0.38/0.61  thf(t48_pre_topc, axiom,
% 0.38/0.61    (![A:$i]:
% 0.38/0.61     ( ( l1_pre_topc @ A ) =>
% 0.38/0.61       ( ![B:$i]:
% 0.38/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.61           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.38/0.61  thf('35', plain,
% 0.38/0.61      (![X14 : $i, X15 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.38/0.61          | (r1_tarski @ X14 @ (k2_pre_topc @ X15 @ X14))
% 0.38/0.61          | ~ (l1_pre_topc @ X15))),
% 0.38/0.61      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.38/0.61  thf('36', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (l1_pre_topc @ sk_A)
% 0.38/0.61          | (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ 
% 0.38/0.61             (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ X0))))),
% 0.38/0.61      inference('sup-', [status(thm)], ['34', '35'])).
% 0.38/0.61  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('38', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ 
% 0.38/0.61          (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ X0)))),
% 0.38/0.61      inference('demod', [status(thm)], ['36', '37'])).
% 0.38/0.61  thf('39', plain,
% 0.38/0.61      (((k3_xboole_0 @ sk_B @ sk_C)
% 0.38/0.61         = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.38/0.61      inference('demod', [status(thm)], ['25', '38'])).
% 0.38/0.61  thf('40', plain,
% 0.38/0.61      (((k2_pre_topc @ sk_A @ 
% 0.38/0.61         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))
% 0.38/0.61         != (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.61             (k2_pre_topc @ sk_A @ sk_B) @ (k2_pre_topc @ sk_A @ sk_C)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('41', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.38/0.61      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.38/0.61  thf('42', plain,
% 0.38/0.61      (((k2_pre_topc @ sk_A @ 
% 0.38/0.61         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))
% 0.38/0.61         != (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.61             (k2_pre_topc @ sk_A @ sk_C)))),
% 0.38/0.61      inference('demod', [status(thm)], ['40', '41'])).
% 0.38/0.61  thf('43', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.38/0.61           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.38/0.61      inference('sup-', [status(thm)], ['13', '14'])).
% 0.38/0.61  thf('44', plain, (((k2_pre_topc @ sk_A @ sk_C) = (sk_C))),
% 0.38/0.61      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.38/0.61  thf('45', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.38/0.61           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.38/0.61      inference('sup-', [status(thm)], ['13', '14'])).
% 0.38/0.61  thf('46', plain,
% 0.38/0.61      (((k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 0.38/0.61         != (k3_xboole_0 @ sk_B @ sk_C))),
% 0.38/0.61      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 0.38/0.61  thf('47', plain, ($false),
% 0.38/0.61      inference('simplify_reflect-', [status(thm)], ['39', '46'])).
% 0.38/0.61  
% 0.38/0.61  % SZS output end Refutation
% 0.38/0.61  
% 0.38/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
