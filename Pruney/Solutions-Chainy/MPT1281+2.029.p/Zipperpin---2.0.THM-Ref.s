%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XglwxQhLJ1

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:48 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 138 expanded)
%              Number of leaves         :   25 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :  605 (1603 expanded)
%              Number of equality atoms :   20 (  26 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(t103_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v5_tops_1 @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v5_tops_1 @ B @ A )
             => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t103_tops_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v5_tops_1 @ B @ A )
          <=> ( B
              = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v5_tops_1 @ X11 @ X12 )
      | ( X11
        = ( k2_pre_topc @ X12 @ ( k1_tops_1 @ X12 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d7_tops_1])).

thf('3',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( sk_B
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v5_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v5_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['0','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('10',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('15',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) )
      | ( ( k4_subset_1 @ X9 @ X8 @ X10 )
        = ( k2_xboole_0 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
        = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('22',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( k2_pre_topc @ X18 @ X17 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X18 ) @ X17 @ ( k2_tops_1 @ X18 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('26',plain,
    ( sk_B
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k2_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) @ ( k2_tops_1 @ A @ B ) ) ) ) )).

thf('28',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X20 @ ( k1_tops_1 @ X20 @ X19 ) ) @ ( k2_tops_1 @ X20 @ X19 ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t71_tops_1])).

thf('29',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('32',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('33',plain,
    ( ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t72_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ ( k2_tops_1 @ A @ B ) ) ) ) )).

thf('35',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X22 @ ( k2_pre_topc @ X22 @ X21 ) ) @ ( k2_tops_1 @ X22 @ X21 ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t72_tops_1])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('39',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','39'])).

thf('41',plain,
    ( sk_B
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','40'])).

thf('42',plain,
    ( sk_B
    = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['20','41'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('43',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('44',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['7','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XglwxQhLJ1
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:50:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.53/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.53/0.71  % Solved by: fo/fo7.sh
% 0.53/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.71  % done 237 iterations in 0.261s
% 0.53/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.53/0.71  % SZS output start Refutation
% 0.53/0.71  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.53/0.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.53/0.71  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 0.53/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.71  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.53/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.71  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.53/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.53/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.53/0.71  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.53/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.71  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.53/0.71  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.53/0.71  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.53/0.71  thf(t103_tops_1, conjecture,
% 0.53/0.71    (![A:$i]:
% 0.53/0.71     ( ( l1_pre_topc @ A ) =>
% 0.53/0.71       ( ![B:$i]:
% 0.53/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.71           ( ( v5_tops_1 @ B @ A ) =>
% 0.53/0.71             ( r1_tarski @
% 0.53/0.71               ( k2_tops_1 @ A @ B ) @ 
% 0.53/0.71               ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.53/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.71    (~( ![A:$i]:
% 0.53/0.71        ( ( l1_pre_topc @ A ) =>
% 0.53/0.71          ( ![B:$i]:
% 0.53/0.71            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.71              ( ( v5_tops_1 @ B @ A ) =>
% 0.53/0.71                ( r1_tarski @
% 0.53/0.71                  ( k2_tops_1 @ A @ B ) @ 
% 0.53/0.71                  ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.53/0.71    inference('cnf.neg', [status(esa)], [t103_tops_1])).
% 0.53/0.71  thf('0', plain,
% 0.53/0.71      (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.53/0.71          (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('1', plain,
% 0.53/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf(d7_tops_1, axiom,
% 0.53/0.71    (![A:$i]:
% 0.53/0.71     ( ( l1_pre_topc @ A ) =>
% 0.53/0.71       ( ![B:$i]:
% 0.53/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.71           ( ( v5_tops_1 @ B @ A ) <=>
% 0.53/0.71             ( ( B ) = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.53/0.71  thf('2', plain,
% 0.53/0.71      (![X11 : $i, X12 : $i]:
% 0.53/0.71         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.53/0.71          | ~ (v5_tops_1 @ X11 @ X12)
% 0.53/0.71          | ((X11) = (k2_pre_topc @ X12 @ (k1_tops_1 @ X12 @ X11)))
% 0.53/0.71          | ~ (l1_pre_topc @ X12))),
% 0.53/0.71      inference('cnf', [status(esa)], [d7_tops_1])).
% 0.53/0.71  thf('3', plain,
% 0.53/0.71      ((~ (l1_pre_topc @ sk_A)
% 0.53/0.71        | ((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.53/0.71        | ~ (v5_tops_1 @ sk_B @ sk_A))),
% 0.53/0.71      inference('sup-', [status(thm)], ['1', '2'])).
% 0.53/0.71  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('5', plain, ((v5_tops_1 @ sk_B @ sk_A)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('6', plain,
% 0.53/0.71      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.53/0.71      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.53/0.71  thf('7', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.53/0.71      inference('demod', [status(thm)], ['0', '6'])).
% 0.53/0.71  thf('8', plain,
% 0.53/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf(dt_k2_tops_1, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( ( l1_pre_topc @ A ) & 
% 0.53/0.71         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.53/0.71       ( m1_subset_1 @
% 0.53/0.71         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.53/0.71  thf('9', plain,
% 0.53/0.71      (![X15 : $i, X16 : $i]:
% 0.53/0.71         (~ (l1_pre_topc @ X15)
% 0.53/0.71          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.53/0.71          | (m1_subset_1 @ (k2_tops_1 @ X15 @ X16) @ 
% 0.53/0.71             (k1_zfmisc_1 @ (u1_struct_0 @ X15))))),
% 0.53/0.71      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.53/0.71  thf('10', plain,
% 0.53/0.71      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.53/0.71         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.53/0.71        | ~ (l1_pre_topc @ sk_A))),
% 0.53/0.71      inference('sup-', [status(thm)], ['8', '9'])).
% 0.53/0.71  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('12', plain,
% 0.53/0.71      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.53/0.71        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.71      inference('demod', [status(thm)], ['10', '11'])).
% 0.53/0.71  thf('13', plain,
% 0.53/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf(dt_k1_tops_1, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( ( l1_pre_topc @ A ) & 
% 0.53/0.71         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.53/0.71       ( m1_subset_1 @
% 0.53/0.71         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.53/0.71  thf('14', plain,
% 0.53/0.71      (![X13 : $i, X14 : $i]:
% 0.53/0.71         (~ (l1_pre_topc @ X13)
% 0.53/0.71          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.53/0.71          | (m1_subset_1 @ (k1_tops_1 @ X13 @ X14) @ 
% 0.53/0.71             (k1_zfmisc_1 @ (u1_struct_0 @ X13))))),
% 0.53/0.71      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.53/0.71  thf('15', plain,
% 0.53/0.71      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.53/0.71         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.53/0.71        | ~ (l1_pre_topc @ sk_A))),
% 0.53/0.71      inference('sup-', [status(thm)], ['13', '14'])).
% 0.53/0.71  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('17', plain,
% 0.53/0.71      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.53/0.71        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.71      inference('demod', [status(thm)], ['15', '16'])).
% 0.53/0.71  thf(redefinition_k4_subset_1, axiom,
% 0.53/0.71    (![A:$i,B:$i,C:$i]:
% 0.53/0.71     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.53/0.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.53/0.71       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.53/0.71  thf('18', plain,
% 0.53/0.71      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.53/0.71         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.53/0.71          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9))
% 0.53/0.71          | ((k4_subset_1 @ X9 @ X8 @ X10) = (k2_xboole_0 @ X8 @ X10)))),
% 0.53/0.71      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.53/0.71  thf('19', plain,
% 0.53/0.71      (![X0 : $i]:
% 0.53/0.71         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.53/0.71            = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))
% 0.53/0.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.53/0.71      inference('sup-', [status(thm)], ['17', '18'])).
% 0.53/0.71  thf('20', plain,
% 0.53/0.71      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.53/0.71         (k2_tops_1 @ sk_A @ sk_B))
% 0.53/0.71         = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['12', '19'])).
% 0.53/0.71  thf('21', plain,
% 0.53/0.71      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.53/0.71        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.71      inference('demod', [status(thm)], ['15', '16'])).
% 0.53/0.71  thf(t65_tops_1, axiom,
% 0.53/0.71    (![A:$i]:
% 0.53/0.71     ( ( l1_pre_topc @ A ) =>
% 0.53/0.71       ( ![B:$i]:
% 0.53/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.71           ( ( k2_pre_topc @ A @ B ) =
% 0.53/0.71             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.53/0.71  thf('22', plain,
% 0.53/0.71      (![X17 : $i, X18 : $i]:
% 0.53/0.71         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.53/0.71          | ((k2_pre_topc @ X18 @ X17)
% 0.53/0.71              = (k4_subset_1 @ (u1_struct_0 @ X18) @ X17 @ 
% 0.53/0.71                 (k2_tops_1 @ X18 @ X17)))
% 0.53/0.71          | ~ (l1_pre_topc @ X18))),
% 0.53/0.71      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.53/0.71  thf('23', plain,
% 0.53/0.71      ((~ (l1_pre_topc @ sk_A)
% 0.53/0.71        | ((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.53/0.71            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.71               (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.53/0.71               (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.53/0.71      inference('sup-', [status(thm)], ['21', '22'])).
% 0.53/0.71  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('25', plain,
% 0.53/0.71      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.53/0.71      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.53/0.71  thf('26', plain,
% 0.53/0.71      (((sk_B)
% 0.53/0.71         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.53/0.71            (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.53/0.71      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.53/0.71  thf('27', plain,
% 0.53/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf(t71_tops_1, axiom,
% 0.53/0.71    (![A:$i]:
% 0.53/0.71     ( ( l1_pre_topc @ A ) =>
% 0.53/0.71       ( ![B:$i]:
% 0.53/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.71           ( r1_tarski @
% 0.53/0.71             ( k2_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) @ ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 0.53/0.71  thf('28', plain,
% 0.53/0.71      (![X19 : $i, X20 : $i]:
% 0.53/0.71         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.53/0.71          | (r1_tarski @ (k2_tops_1 @ X20 @ (k1_tops_1 @ X20 @ X19)) @ 
% 0.53/0.71             (k2_tops_1 @ X20 @ X19))
% 0.53/0.71          | ~ (l1_pre_topc @ X20))),
% 0.53/0.71      inference('cnf', [status(esa)], [t71_tops_1])).
% 0.53/0.71  thf('29', plain,
% 0.53/0.71      ((~ (l1_pre_topc @ sk_A)
% 0.53/0.71        | (r1_tarski @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.53/0.71           (k2_tops_1 @ sk_A @ sk_B)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['27', '28'])).
% 0.53/0.71  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('31', plain,
% 0.53/0.71      ((r1_tarski @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.53/0.71        (k2_tops_1 @ sk_A @ sk_B))),
% 0.53/0.71      inference('demod', [status(thm)], ['29', '30'])).
% 0.53/0.71  thf(d10_xboole_0, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.53/0.71  thf('32', plain,
% 0.53/0.71      (![X0 : $i, X2 : $i]:
% 0.53/0.71         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.53/0.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.53/0.71  thf('33', plain,
% 0.53/0.71      ((~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.53/0.71           (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.53/0.71        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.71            = (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.53/0.71      inference('sup-', [status(thm)], ['31', '32'])).
% 0.53/0.71  thf('34', plain,
% 0.53/0.71      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.53/0.71        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.71      inference('demod', [status(thm)], ['15', '16'])).
% 0.53/0.71  thf(t72_tops_1, axiom,
% 0.53/0.71    (![A:$i]:
% 0.53/0.71     ( ( l1_pre_topc @ A ) =>
% 0.53/0.71       ( ![B:$i]:
% 0.53/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.71           ( r1_tarski @
% 0.53/0.71             ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ 
% 0.53/0.71             ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 0.53/0.71  thf('35', plain,
% 0.53/0.71      (![X21 : $i, X22 : $i]:
% 0.53/0.71         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.53/0.71          | (r1_tarski @ (k2_tops_1 @ X22 @ (k2_pre_topc @ X22 @ X21)) @ 
% 0.53/0.71             (k2_tops_1 @ X22 @ X21))
% 0.53/0.71          | ~ (l1_pre_topc @ X22))),
% 0.53/0.71      inference('cnf', [status(esa)], [t72_tops_1])).
% 0.53/0.71  thf('36', plain,
% 0.53/0.71      ((~ (l1_pre_topc @ sk_A)
% 0.53/0.71        | (r1_tarski @ 
% 0.53/0.71           (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 0.53/0.71           (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.53/0.71      inference('sup-', [status(thm)], ['34', '35'])).
% 0.53/0.71  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('38', plain,
% 0.53/0.71      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.53/0.71      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.53/0.71  thf('39', plain,
% 0.53/0.71      ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.53/0.71        (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.53/0.71      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.53/0.71  thf('40', plain,
% 0.53/0.71      (((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.71         = (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.53/0.71      inference('demod', [status(thm)], ['33', '39'])).
% 0.53/0.71  thf('41', plain,
% 0.53/0.71      (((sk_B)
% 0.53/0.71         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.53/0.71            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.53/0.71      inference('demod', [status(thm)], ['26', '40'])).
% 0.53/0.71  thf('42', plain,
% 0.53/0.71      (((sk_B)
% 0.53/0.71         = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.53/0.71      inference('sup+', [status(thm)], ['20', '41'])).
% 0.53/0.71  thf(t36_xboole_1, axiom,
% 0.53/0.71    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.53/0.71  thf('43', plain,
% 0.53/0.71      (![X3 : $i, X4 : $i]: (r1_tarski @ (k4_xboole_0 @ X3 @ X4) @ X3)),
% 0.53/0.71      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.53/0.71  thf(t44_xboole_1, axiom,
% 0.53/0.71    (![A:$i,B:$i,C:$i]:
% 0.53/0.71     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.53/0.71       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.53/0.71  thf('44', plain,
% 0.53/0.71      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.53/0.71         ((r1_tarski @ X5 @ (k2_xboole_0 @ X6 @ X7))
% 0.53/0.71          | ~ (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X7))),
% 0.53/0.71      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.53/0.71  thf('45', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.53/0.71      inference('sup-', [status(thm)], ['43', '44'])).
% 0.53/0.71  thf('46', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.53/0.71      inference('sup+', [status(thm)], ['42', '45'])).
% 0.53/0.71  thf('47', plain, ($false), inference('demod', [status(thm)], ['7', '46'])).
% 0.53/0.71  
% 0.53/0.71  % SZS output end Refutation
% 0.53/0.71  
% 0.53/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
